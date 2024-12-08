use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter},
    literal::{Literal, LiteralManager, Polarity, Variable, VariableIdx},
    manager::{
        dimacs,
        model::Models,
        options::{GarbageCollection, SddOptions},
    },
    sdd::{Decision, Element, Sdd, SddId, SddRef, SddType},
    util::set_bits_indices,
    vtree::{
        rotate_partition_left, rotate_partition_right, split_nodes_for_left_rotate,
        split_nodes_for_right_rotate, split_nodes_for_swap, swap_partition, Direction, Fragment,
        LeftRotateSplit, RightRotateSplit, VTreeIdx, VTreeManager, VTreeOrder, VTreeRef,
    },
};
use bitvec::prelude::*;
use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::{BTreeSet, HashMap},
    ops::BitOr,
};
use tracing::instrument;

use super::options::{FragmentHeuristic, MinimizationCutoff};

#[derive(Clone, Eq, PartialEq, Hash, Debug, Copy)]
pub(crate) enum Operation {
    Conjoin,
    Disjoin,
}

impl Operation {
    /// Get the absorbing element with respect to the Boolean operation.
    fn zero(self) -> SddId {
        match self {
            Operation::Conjoin => FALSE_SDD_IDX,
            Operation::Disjoin => TRUE_SDD_IDX,
        }
    }
}

pub(crate) enum CachedOperation {
    BinOp(SddId, Operation, SddId),
    Neg(SddId),
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
struct Entry {
    fst: SddId,
    snd: SddId,
    op: Operation,
}

impl Entry {
    fn contains_id(&self, id: SddId) -> bool {
        self.fst == id || self.snd == id
    }
}

#[derive(Debug, Clone)]
pub struct GCStatistics {
    pub nodes_collected: usize,
    pub gc_triggered: usize,
}

impl GCStatistics {
    fn collected(&mut self, nodes_collected: usize) {
        self.gc_triggered += 1;
        self.nodes_collected += nodes_collected;
    }
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct SddManager {
    options: SddOptions,

    vtree_manager: RefCell<VTreeManager>,
    literal_manager: RefCell<LiteralManager>,

    // Unique table holding all the decision nodes.
    // More details can be found in [Algorithms and Data Structures in VLSI Design](https://link.springer.com/book/10.1007/978-3-642-58940-9).
    unique_table: RefCell<HashMap<SddId, SddRef>>,

    // Caches all the computations.
    op_cache: RefCell<HashMap<Entry, SddId>>,
    neg_cache: RefCell<HashMap<SddId, SddId>>,

    next_idx: RefCell<SddId>,

    // Flag denoting whether we are doing rotations. If so, garbage collection
    // is turned off.
    rotating: RefCell<bool>,

    gc_stats: RefCell<GCStatistics>,
}

// True and false SDDs have indicies 0 and 1 throughout the whole computation.
pub(crate) const FALSE_SDD_IDX: SddId = SddId(0);
pub(crate) const TRUE_SDD_IDX: SddId = SddId(1);

impl SddManager {
    /// # Panics
    ///
    /// TODO
    #[must_use]
    pub fn new(options: &SddOptions) -> SddManager {
        let mut unique_table = RefCell::new(HashMap::new());
        let ff = SddRef::new(Sdd::new_false());
        let tt = SddRef::new(Sdd::new_true());

        assert_eq!(tt.id(), TRUE_SDD_IDX);
        assert_eq!(ff.id(), FALSE_SDD_IDX);

        unique_table.get_mut().insert(tt.id(), tt);
        unique_table.get_mut().insert(ff.id(), ff);

        let variables: Vec<_> = options
            .variables
            .iter()
            .enumerate()
            .map(|(idx, variable)| Variable::new(variable, u32::try_from(idx).unwrap()))
            .collect();

        let manager = SddManager {
            options: options.clone(),
            op_cache: RefCell::new(HashMap::new()),
            neg_cache: RefCell::new(HashMap::new()),
            next_idx: RefCell::new(SddId(2)), // Account for ff and tt created earlier which have indices 0 and 1.
            vtree_manager: RefCell::new(VTreeManager::new(options.vtree_strategy, &variables)),
            literal_manager: RefCell::new(LiteralManager::new()),
            rotating: RefCell::new(false),
            gc_stats: RefCell::new(GCStatistics {
                nodes_collected: 0,
                gc_triggered: 0,
            }),
            unique_table,
        };

        for variable in variables {
            let vtree = manager
                .vtree_manager
                .borrow()
                .get_variable_vtree(&variable)
                .unwrap();

            let positive_literal = manager.new_sdd_from_type(
                SddType::Literal(Literal::new_with_label(
                    Polarity::Positive,
                    variable.clone(),
                )),
                vtree.clone(),
                None,
            );

            let negative_literal = manager.new_sdd_from_type(
                SddType::Literal(Literal::new_with_label(
                    Polarity::Negative,
                    variable.clone(),
                )),
                vtree.clone(),
                None,
            );

            manager.literal_manager.borrow().add_variable(
                &variable,
                positive_literal,
                negative_literal,
            );
        }

        manager
    }

    /// Parse a CNF in [DIMACS] format and construct an SDD. Function expects there is a
    /// sufficient number of variables already defined in the manager and tries to map
    /// variable indices in DIMACS to their string representations.
    ///
    /// # Errors
    ///
    /// TODO
    ///
    /// [DIMACS]: https://www21.in.tum.de/~lammich/2015_SS_Seminar_SAT/resources/dimacs-cnf.pdf
    pub fn from_dimacs(
        &self,
        reader: &mut dyn std::io::Read,
        create_variables: bool,
    ) -> Result<SddRef, String> {
        // TODO: Timing

        let mut reader = std::io::BufReader::new(reader);
        let mut dimacs = dimacs::DimacsReader::new(&mut reader);

        let preamble = dimacs.parse_preamble().map_err(|err| err.to_string())?;
        let num_variables = self.literal_manager.borrow().len();
        if !create_variables && preamble.variables > num_variables {
            return Err(String::from(
                "preamble specifies more variables than those present in the manager",
            ));
        }

        let mut sdd = self.tautology();
        let mut i = 0;
        loop {
            match dimacs.parse_next_clause().map_err(|err| err.to_string())? {
                None => return Ok(sdd),
                Some(clause) => {
                    sdd = self.conjoin(&sdd, &clause.to_sdd(self));

                    if i != 0
                        && self.options.minimize_after != 0
                        && i % self.options.minimize_after == 0
                    {
                        tracing::info!(
                            sdd_id = sdd.id().0,
                            size = self.size(&sdd),
                            "before minimizing"
                        );
                        self.minimize(
                            self.options.minimization_cutoff,
                            self.options.fragment_heuristic,
                            &sdd,
                        );
                        tracing::info!(
                            sdd_id = sdd.id().0,
                            size = self.size(&sdd),
                            "after minimizing"
                        );
                    }

                    if self.should_collect_garbage(&sdd) {
                        self.collect_garbage();
                    }

                    i += 1;
                }
            }
        }
    }

    pub(crate) fn try_get_node(&self, id: SddId) -> Option<SddRef> {
        self.unique_table.borrow().get(&id).cloned()
    }

    /// # Panics
    /// Function panics if there is no such node with the corresponding id in the unique table.
    #[must_use]
    pub(crate) fn get_node(&self, id: SddId) -> SddRef {
        self.unique_table
            .borrow()
            .get(&id)
            .unwrap_or_else(|| panic!("SDD {id} is not in the unique_table"))
            .clone()
    }

    pub(crate) fn get_nodes_normalized_for(&self, vtree_idx: VTreeIdx) -> Vec<(SddId, SddRef)> {
        self.unique_table
            .borrow()
            .iter()
            .filter(|(_, sdd)| sdd.vtree().index() == vtree_idx)
            .map(|(id, sdd)| (*id, sdd.clone()))
            .collect()
    }

    pub(crate) fn remove_node(&self, id: SddId) -> Result<(), ()> {
        tracing::debug!(id = id.0, "removing node from cache");
        let entries: Vec<_> = {
            self.op_cache
                .borrow()
                .iter()
                .filter(|(entry, res)| entry.contains_id(id) || **res == id)
                .map(|(entry, res)| (entry.clone(), *res))
                .collect()
        };

        for (entry, _) in entries {
            _ = self.op_cache.borrow_mut().remove(&entry).unwrap();
        }

        match self.unique_table.borrow_mut().remove(&id) {
            Some(..) => Ok(()),
            None => Err(()),
        }
    }

    fn remove_from_op_cache(&self, ids: &BTreeSet<SddId>) {
        let entries_to_remove: Vec<_> = ids
            .iter()
            .map(|id| (id, self.get_cached_operation(&CachedOperation::Neg(*id))))
            .filter(|(_, negation)| negation.is_some())
            .map(|(fst, snd)| (fst, snd.unwrap()))
            .collect();

        let mut cache = self.neg_cache.borrow_mut();
        for (fst, snd) in &entries_to_remove {
            cache.remove(fst);
            cache.remove(snd);
        }

        let mut entries_to_remove = Vec::new();
        for (entry @ Entry { fst, snd, .. }, res) in self.op_cache.borrow().iter() {
            if ids.contains(fst) || ids.contains(snd) || ids.contains(res) {
                entries_to_remove.push(entry.clone());
            }
        }

        let mut cache = self.op_cache.borrow_mut();
        for entry in &entries_to_remove {
            cache.remove(entry);
        }

        let mut unique_table = self.unique_table.borrow_mut();
        for id in ids {
            unique_table.remove(id);
        }
    }

    /// # Panics
    ///
    /// TODO
    pub fn literal(&self, literal: &str, polarity: Polarity) -> SddRef {
        let Some((_, variants)) = self.literal_manager.borrow().find_by_label(literal) else {
            // TODO: We should return proper error instead of panicking here.
            panic!("literal '{literal}' has not been created!");
        };

        variants.get(polarity)
    }

    pub(crate) fn literal_from_idx(&self, idx: VariableIdx, polarity: Polarity) -> SddRef {
        let Some((_, variants)) = self.literal_manager.borrow().find_by_index(idx) else {
            // TODO: We should return proper error instead of panicking here.
            panic!("literal with index {idx:?} has not been created!");
        };

        variants.get(polarity)
    }

    /// # Panics
    ///
    /// TODO
    pub fn tautology(&self) -> SddRef {
        self.try_get_node(TRUE_SDD_IDX)
            .expect("True SDD node must be present in the unique table at all times")
    }

    /// # Panics
    ///
    /// TODO
    pub fn contradiction(&self) -> SddRef {
        self.try_get_node(FALSE_SDD_IDX)
            .expect("False SDD node must be present in the unique table at all times")
    }

    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn conjoin(&self, fst: &SddRef, snd: &SddRef) -> SddRef {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0);
        if fst == snd {
            return fst.clone();
        }

        if fst.is_false() {
            return fst.clone();
        }

        if snd.is_false() {
            return snd.clone();
        }

        if fst.is_true() {
            return snd.clone();
        }

        if snd.is_true() {
            return fst.clone();
        }

        if fst.eq_negated(snd, self) {
            return self.contradiction();
        }

        self.apply(fst, snd, Operation::Conjoin)
    }

    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn disjoin(&self, fst: &SddRef, snd: &SddRef) -> SddRef {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0);
        if fst == snd {
            return fst.clone();
        }

        if fst.is_true() {
            return fst.clone();
        }

        if snd.is_true() {
            return snd.clone();
        }

        if fst.is_false() {
            return snd.clone();
        }

        if snd.is_false() {
            return fst.clone();
        }

        if fst.eq_negated(snd, self) {
            return self.tautology();
        }

        self.apply(fst, snd, Operation::Disjoin)
    }

    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn negate(&self, fst: &SddRef) -> SddRef {
        tracing::debug!(fst_id = fst.id().0);
        fst.clone().negate(self)
    }

    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn imply(&self, fst: &SddRef, snd: &SddRef) -> SddRef {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0);
        if fst == snd && fst.is_true() {
            return snd.clone();
        }

        if fst.is_false() {
            return self.tautology();
        }

        if fst.is_true() {
            return snd.clone();
        }

        if fst.eq_negated(snd, self) {
            return snd.clone();
        }

        // Relies on the fact that A => B is equivalent to !A || B.
        self.apply(&fst.negate(self), snd, Operation::Disjoin)
    }

    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn equiv(&self, fst: &SddRef, snd: &SddRef) -> SddRef {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0);
        if fst == snd {
            return self.tautology();
        }

        if fst.eq_negated(snd, self) {
            return self.contradiction();
        }

        // Relies on the fact that A <=> B is equivalent (!A && !B) || (A && B).
        let fst_con = self.conjoin(&fst.negate(self), &snd.negate(self));
        let snd_con = self.conjoin(fst, snd);
        self.disjoin(&fst_con, &snd_con)
    }

    /// Enumerate all models of the SDD. This method eagerly computes all satisfying assignments.
    pub fn model_enumeration(&self, sdd: &SddRef) -> Models {
        let mut models: Vec<BitVec> = Vec::new();
        self._model_enumeration(sdd, &mut models);

        let all_variables: BTreeSet<_> = self.literal_manager.borrow().all_variables();
        let unbound_variables: Vec<_> = all_variables
            .difference(&self.get_variables(sdd))
            .cloned()
            .collect();
        SddManager::expand_models(&mut models, &unbound_variables);
        Models::new(&models, all_variables.iter().cloned().collect())
    }

    /// # Panics
    ///
    /// TODO
    pub fn model_count(&self, sdd: &SddRef) -> u64 {
        let models = self._model_count(sdd);

        if self.vtree_manager.borrow().root_idx().unwrap() == sdd.vtree().index() {
            return models;
        }

        let sdd_variables = self
            .vtree_manager
            .borrow()
            .get_vtree(sdd.vtree().index())
            .unwrap()
            .0
            .borrow()
            .get_variables()
            .len();
        let unbound = self.literal_manager.borrow().len() - sdd_variables;

        models * 2_u64.pow(u32::try_from(unbound).unwrap())
    }

    fn create_fragment(&self, fragment_strategy: &FragmentHeuristic) -> Fragment {
        match fragment_strategy {
            FragmentHeuristic::Root => {
                let root = self.root().unwrap();
                if root.right_child().is_internal() {
                    Fragment::new(&root, &root.right_child())
                } else {
                    Fragment::new(&root, &root.left_child())
                }
            }
            FragmentHeuristic::Random => unimplemented!(),
            FragmentHeuristic::Custom(idx, linearity) => unimplemented!(),
            FragmentHeuristic::MostNormalized => {
                // There are 2n-1 nodes in the vtree where n is the number
                // of variables.
                let nodes = 2 * self.options.variables.len() - 1;
                let mut frequency = vec![0; nodes];
                for sdd in self.unique_table.borrow().values() {
                    if sdd.is_constant_or_literal() {
                        continue;
                    }
                    frequency[sdd.vtree().index().0 as usize] += 1;
                }

                let root_idx = frequency
                    .iter()
                    .enumerate()
                    .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(Ordering::Equal))
                    .map(|(index, _)| index)
                    .unwrap();
                let root = self
                    .vtree_manager
                    .borrow()
                    .get_vtree(VTreeIdx(root_idx as u32))
                    .unwrap();

                assert!(root.is_internal());
                let lc = root.left_child();
                let rc = root.right_child();

                let child = if frequency[lc.index().0 as usize] > frequency[rc.index().0 as usize]
                    && lc.is_internal()
                {
                    lc
                } else if rc.is_internal() {
                    rc
                } else {
                    panic!("none of left and right child are internal nodes, we have to do something else here");
                };

                println!("frequencies: {frequency:?}");
                println!("=> root {:?}, child {:?}", root.index(), child.index());

                Fragment::new(&root, &child)
            }
        }
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn minimize(
        &self,
        cut_off: MinimizationCutoff,
        fragment_strategy: FragmentHeuristic,
        reference_sdd: &SddRef,
    ) {
        println!(
            "\nreference_sdd size before: {:?}",
            self.size(reference_sdd)
        );
        let mut fragment = self.create_fragment(&fragment_strategy);

        // TODO: Remove sanity checks.
        // let models = self.model_enumeration(reference_sdd);
        tracing::debug!(
            sdd_id = reference_sdd.id().0,
            size = self.size(reference_sdd)
        );

        let init_size = self.size(reference_sdd);
        let mut i = 0;
        let mut best_i: usize = 0;
        let mut best_size = init_size;
        let mut curr_size = init_size;
        for _ in 0..12 {
            fragment.next(&Direction::Forward, self);
            tracing::debug!(
                iteration = i,
                sdd_id = reference_sdd.id().0,
                size = self.size(reference_sdd)
            );

            debug_assert!(reference_sdd.is_trimmed(&self));
            debug_assert!(reference_sdd.is_compressed(&self));

            // TODO: Improve the assertion by doing the first model_enumeration in debug as well.
            // println!("\n({i})\n{}", self.model_enumeration(reference_sdd));

            curr_size = self.size(reference_sdd);
            println!("({i}): new size: {curr_size}");
            if curr_size < best_size {
                // We have found better vtree, mark the state we found it in so we can come
                // back to it once we go through all fragment configurations.
                println!("found new best at {i}: {best_size} ~> {curr_size}");
                best_size = curr_size;
                best_i = i;
            }

            if SddManager::should_stop_minimizing(cut_off, init_size, curr_size, i) {
                if best_i == i || curr_size == best_size {
                    // We have fulfilled the searching criteria and the current vtree configuration
                    // makes the reference sdd sufficiently small.
                    println!("will stop minimizing => no need to rewind => return immediatelly");
                    println!("reference_sdd size after: {:?}\n", self.size(reference_sdd));
                    return;
                }
                // We have fulfilled the searching criteria but we have already iterated over
                // the best vtree configuration. We have to break out and go back to it.
                println!("will stop minimizing => will rewind back to {best_i:?}");
                break;
            }

            i += 1;
        }

        if curr_size == best_size {
            println!("tried all 12 and no need to rewind, returning");
            return;
        }

        // TODO: Instead of rewinding e.g. to the back, select something that is
        // "good enough" and not that far.

        println!("rewinding from {i} to {best_i}");
        fragment.rewind(best_i + 1, self);
        println!("done rewinding...\n");
    }

    fn should_stop_minimizing(
        cut_off: MinimizationCutoff,
        init_size: u64,
        curr_size: u64,
        curr_iter: usize,
    ) -> bool {
        match cut_off {
            MinimizationCutoff::Iteration(after_iter) => curr_iter >= after_iter,
            MinimizationCutoff::Decrease(decrease) => {
                #[allow(clippy::cast_precision_loss)]
                let ratio = curr_size as f64 / init_size as f64;
                ratio - decrease >= f64::EPSILON
            }
            MinimizationCutoff::None => false,
        }
    }

    fn check_table_consistency(&self) {
        for (k, v) in self.unique_table.borrow().iter() {
            if *k != v.id() {}
        }
    }

    pub fn collect_garbage(&self) {
        let mut removed = BTreeSet::new();

        self.check_table_consistency();
        let roots: BTreeSet<_> = self
            .unique_table
            .borrow()
            .values()
            // An SDD is root if there is a single reference to it -- one
            // from the unique_table. It therefore has no parents
            // and the user does not point to it.
            .filter(|sdd| {
                sdd.0.try_borrow().is_ok() && !sdd.is_constant_or_literal() && sdd.strong_count() == 1
            })
            .map(SddRef::id)
            .collect();

        // Mark the roots as removed.
        removed.extend(roots.iter());

        for root in &roots {
            let root = self.get_node(*root);
            // self.remove_from_unique_table(root.id());

            let mut queue: Vec<_> = root
                .elements()
                .unwrap()
                .into_iter()
                .flat_map(|Element { prime, sub }| [prime, sub])
                .collect();
            while !queue.is_empty() {
                let sdd = queue.pop().unwrap();

                // 3 references means orphaned: 1 from unique_table, 1 from parent not present
                // in the unique_table anymore and 1 from here.
                if sdd.strong_count() == 3 && !sdd.is_constant_or_literal() {
                    // Mark the node as removed.
                    removed.insert(sdd.id());
                    // self.remove_from_unique_table(sdd.id());

                    queue.extend(
                        sdd.elements()
                            .unwrap()
                            .into_iter()
                            .flat_map(|Element { prime, sub }| [prime, sub])
                            .filter(|sdd| !sdd.is_constant_or_literal()),
                    );
                }
            }
        }

        // Remove the removed SDDs from computational caches
        // and the unique_table.
        self.remove_from_op_cache(&removed);
        self.gc_stats.borrow_mut().collected(removed.len());
    }

    fn should_collect_garbage(&self, reference: &SddRef) -> bool {
        fn hit_threshold(total_nodes: u64, sdd_size: u64, ratio: f64) -> bool {
            #![allow(clippy::cast_precision_loss)]
            (sdd_size as f64 / total_nodes as f64) < ratio
        }

        match self.options.garbage_collection {
            GarbageCollection::Off => false,
            GarbageCollection::Automatic(ratio) => {
                !*self.rotating.borrow()
                    && hit_threshold(self.total_sdds(), self.size(reference), ratio)
            }
        }
    }

    /// Get the size of the SDD which is the number of elements reachable from it.
    pub fn size(&self, sdd: &SddRef) -> u64 {
        // TODO: Move this function to SddRef.
        fn traverse_and_count(sdd: &SddRef, seen: &mut Vec<SddId>) -> u64 {
            if seen.contains(&sdd.id()) {
                return 0;
            }

            match sdd.0.borrow().sdd_type {
                SddType::Decision(Decision { ref elements }) => {
                    seen.push(sdd.id());

                    elements.len() as u64
                        + elements
                            .iter()
                            .map(Element::get_prime_sub)
                            .map(|(prime, sub)| {
                                traverse_and_count(&prime, seen) + traverse_and_count(&sub, seen)
                            })
                            .sum::<u64>()
                }
                _ => 0,
            }
        }

        let mut seen: Vec<SddId> = Vec::new();
        traverse_and_count(sdd, &mut seen)
    }

    #[instrument(skip_all, level = tracing::Level::DEBUG)]
    fn _model_enumeration(&self, sdd: &SddRef, bitvecs: &mut Vec<BitVec>) {
        tracing::debug!(sdd_id = sdd.id().0);
        // Return the cached value if it already exists.
        if let Some(ref mut models) = sdd.models() {
            tracing::debug!("has {} cached models", models.len());
            bitvecs.append(models);
            return;
        }

        if sdd.is_constant() {
            return;
        }

        let mut all_models = Vec::new();
        {
            // Create a new scope to borrow sdd_type since we will mutate it later on due to caching.
            let sdd_type = &sdd.0.borrow().sdd_type;

            if let SddType::Literal(ref literal) = sdd_type {
                let mut model = bitvec![usize, LocalBits; 0; self.literal_manager.borrow().len()];
                model.set(
                    literal.var_label().index().0 as usize,
                    literal.polarity() == Polarity::Positive,
                );
                bitvecs.push(model);
                return;
            }

            let SddType::Decision(decision) = sdd_type else {
                panic!("every other sddType should've been handled ({sdd_type:?})",);
            };

            let all_variables = self.get_variables(sdd);
            for Element { prime, sub } in &decision.elements {
                let mut models = Vec::new();

                if prime.is_false() || sub.is_false() {
                    continue;
                }

                if prime.is_true() || sub.is_true() {
                    if prime.is_true() {
                        self._model_enumeration(sub, &mut models);
                    } else {
                        self._model_enumeration(prime, &mut models);
                    }
                } else {
                    let mut fst = Vec::new();
                    let mut snd = Vec::new();

                    self._model_enumeration(prime, &mut fst);
                    self._model_enumeration(sub, &mut snd);

                    for fst_bv in &fst {
                        for snd_bv in &snd {
                            models.push(fst_bv.clone().bitor(snd_bv));
                        }
                    }
                }

                let all_reachable_variables = self
                    .get_variables(prime)
                    .union(&self.get_variables(sub))
                    .cloned()
                    .collect();
                let unbound_variables: Vec<_> = all_variables
                    .difference(&all_reachable_variables)
                    .cloned()
                    .collect();

                SddManager::expand_models(&mut models, &unbound_variables);
                all_models.append(&mut models);
            }
        }
        bitvecs.append(&mut all_models);

        sdd.cache_models(bitvecs);
    }

    /// Count number of models for this SDD.
    fn _model_count(&self, sdd: &SddRef) -> u64 {
        // Return the cached value if it already exists.
        if let Some(model_count) = sdd.model_count() {
            return model_count;
        }

        let mut total_models = 0;
        {
            // Create a new scope to borrow sdd_type since we will mutate it later on due to caching.
            let SddType::Decision(ref decision) = sdd.0.borrow().sdd_type else {
                panic!("every other sddType should've been handled");
            };

            let get_models_count = |sdd: &SddRef| {
                if sdd.is_literal() || sdd.is_true() {
                    1
                } else if sdd.is_false() {
                    0
                } else {
                    self._model_count(sdd)
                }
            };

            let all_variables = self.get_variables(sdd).len();

            for Element { prime, sub } in &decision.elements {
                let model_count = get_models_count(prime) * get_models_count(sub);

                // Account for variables that do not appear in neither prime or sub.
                let all_reachable = self
                    .get_variables(prime)
                    .union(&self.get_variables(sub))
                    .count();
                let unbound_variables = all_variables - all_reachable;

                total_models += model_count * 2_u64.pow(u32::try_from(unbound_variables).unwrap());
            }
        }

        sdd.cache_model_count(total_models);
        total_models
    }

    /// # Errors
    ///
    /// TODO
    pub fn draw_all_sdds(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("sdd"), true);
        for node in self.unique_table.borrow().values() {
            node.0.borrow().draw(&mut dot_writer);
        }
        dot_writer.write(writer)
    }

    /// # Errors
    ///
    /// TODO
    pub fn draw_sdd(&self, writer: &mut dyn std::io::Write, sdd: &SddRef) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("sdd"), false);
        let mut seen = BTreeSet::new();

        let mut sdds = vec![sdd.clone()];
        while let Some(sdd) = sdds.pop() {
            if seen.contains(&sdd.id()) {
                continue;
            }

            sdd.0.borrow().draw(&mut dot_writer);
            seen.insert(sdd.id());

            if let SddType::Decision(Decision { ref elements }) = sdd.0.borrow().sdd_type {
                elements
                    .iter()
                    .map(Element::get_prime_sub)
                    .for_each(|(prime, sub)| {
                        sdds.push(prime);
                        sdds.push(sub);
                    });
            };
        }

        dot_writer.write(writer)
    }

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_vtree_graph(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("vtree"), false);
        self.vtree_manager.borrow().draw(&mut dot_writer);
        dot_writer.write(writer)
    }

    /// Apply operation on the two Sdds.
    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn apply(&self, fst: &SddRef, snd: &SddRef, op: Operation) -> SddRef {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "apply");
        let (fst, snd) = if fst.vtree().index() < snd.vtree().index() {
            (fst, snd)
        } else {
            (snd, fst)
        };

        if let Some(result) =
            self.get_cached_operation(&CachedOperation::BinOp(fst.id(), op, snd.id()))
        {
            tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "cached");
            return self.get_node(result);
        }

        let (lca, order) = self
            .vtree_manager
            .borrow()
            .least_common_ancestor(fst.vtree().index(), snd.vtree().index());

        let elements = match order {
            VTreeOrder::Equal => self._apply_eq(fst, snd, op),
            VTreeOrder::Inequal => self._apply_ineq(fst, snd, op),
            VTreeOrder::LeftSubOfRight => self._apply_left_sub_of_right(fst, snd, op),
            VTreeOrder::RightSubOfLeft => self._apply_right_sub_of_left(fst, snd, op),
        };

        let sdd = Sdd::unique_d(&elements, &lca, self).canonicalize(&self);
        self.insert_node(&sdd);
        self.cache_operation(&CachedOperation::BinOp(fst.id(), op, snd.id()), sdd.id());

        debug_assert!(sdd.is_trimmed(self));
        debug_assert!(sdd.is_compressed(self));

        sdd
    }

    pub fn gc_statistics(&self) -> GCStatistics {
        self.gc_stats.borrow().clone()
    }

    pub fn total_sdds(&self) -> u64 {
        self.unique_table.borrow().len() as u64
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn _apply_eq(&self, fst: &SddRef, snd: &SddRef, op: Operation) -> BTreeSet<Element> {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "apply_eq");
        assert_eq!(fst.vtree().index(), snd.vtree().index());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let mut elements = BTreeSet::new();
        for Element {
            prime: fst_prime,
            sub: fst_sub,
        } in &fst.0.borrow().expand(self).elements
        {
            for Element {
                prime: snd_prime,
                sub: snd_sub,
            } in &snd.0.borrow().expand(self).elements
            {
                let res_prime = self.conjoin(fst_prime, snd_prime);

                if !res_prime.is_false() {
                    let res_sub = match op {
                        Operation::Conjoin => self.conjoin(fst_sub, snd_sub),
                        Operation::Disjoin => self.disjoin(fst_sub, snd_sub),
                    };

                    if res_sub.is_true() && res_prime.is_true() {
                        println!(
                            "_apply_eq: we can optimize since res_sub and res_prime are both true"
                        );
                    }

                    elements.insert(Element {
                        prime: res_prime,
                        sub: res_sub,
                    });
                }
            }
        }

        elements
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn _apply_ineq(&self, fst: &SddRef, snd: &SddRef, op: Operation) -> BTreeSet<Element> {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "apply_ineq");
        assert!(fst.vtree().index() < snd.vtree().index());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let fst_negated = fst.negate(self);

        let apply = |fst: &SddRef, snd: &SddRef| {
            if op == Operation::Conjoin {
                self.conjoin(fst, snd)
            } else {
                self.disjoin(fst, snd)
            }
        };

        let tt = self.tautology();
        let ff = self.contradiction();

        btreeset!(
            Element {
                prime: fst.clone(),
                sub: apply(snd, &tt),
            },
            Element {
                prime: fst_negated,
                sub: apply(snd, &ff),
            }
        )
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub(crate) fn _conjoin_rotations(&self, fst: &SddRef, snd: &SddRef, lca: &VTreeRef) -> SddRef {
        if fst.is_false() || snd.is_false() {
            return self.contradiction();
        }

        if fst.is_true() {
            return snd.clone();
        }

        if snd.is_true() {
            return fst.clone();
        }

        if let Some(result) = self.get_cached_operation(&CachedOperation::BinOp(
            fst.id(),
            Operation::Conjoin,
            snd.id(),
        )) {
            return self.get_node(result);
        }

        let elements = btreeset!(
            Element {
                prime: fst.clone(),
                sub: snd.clone(),
            },
            Element {
                prime: self.negate(fst),
                sub: self.contradiction(),
            }
        );

        let sdd = Sdd::unique_d(&elements, lca, self);
        sdd.canonicalize(self);

        self.insert_node(&sdd);
        self.cache_operation(
            &CachedOperation::BinOp(fst.id(), Operation::Conjoin, snd.id()),
            sdd.id(),
        );

        sdd
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn _apply_left_sub_of_right(
        &self,
        fst: &SddRef,
        snd: &SddRef,
        op: Operation,
    ) -> BTreeSet<Element> {
        tracing::debug!(
            fst_id = fst.id().0,
            snd_id = snd.id().0,
            ?op,
            "apply_left_sub_of_right"
        );
        assert!(fst.vtree().index() < snd.vtree().index());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let new_node = if op == Operation::Conjoin {
            fst
        } else {
            &fst.negate(self)
        };

        let snd_elements = snd.0.borrow().sdd_type.elements().unwrap_or_else(||
            panic!(
                "snd of _apply_left_sub_of_right must be a decision node but was instead {} (id {})",
                snd.0.borrow().sdd_type.name(),
                snd.id(),
            )
        );

        let mut elements = btreeset!(Element {
            prime: self.negate(new_node),
            sub: self.get_node(op.zero()),
        });

        for Element {
            prime: snd_prime,
            sub: snd_sub,
        } in snd_elements
        {
            let new_prime = self.conjoin(&snd_prime, new_node);
            if !new_prime.is_false() {
                elements.insert(Element {
                    prime: new_prime,
                    sub: snd_sub,
                });
            }
        }

        elements
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn _apply_right_sub_of_left(
        &self,
        fst: &SddRef,
        snd: &SddRef,
        op: Operation,
    ) -> BTreeSet<Element> {
        tracing::debug!(
            fst_id = fst.id().0,
            snd_id = snd.id().0,
            ?op,
            "apply_right_sub_of_left"
        );
        assert!(fst.vtree().index() < snd.vtree().index());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let fst_elements = fst.0.borrow().sdd_type.elements().unwrap_or_else(||
            panic!(
                "fst of _apply_right_sub_of_left must be a decision node but was instead {} (id {})",
                fst.0.borrow().sdd_type.name(),
                fst.id(),
            )
        );

        let mut elements = BTreeSet::new();

        for Element {
            prime: fst_prime,
            sub: fst_sub,
        } in fst_elements
        {
            let new_sub = match op {
                Operation::Conjoin => self.conjoin(&fst_sub, snd),
                Operation::Disjoin => self.disjoin(&fst_sub, snd),
            };

            elements.insert(Element {
                prime: fst_prime,
                sub: new_sub,
            });
        }

        elements
    }

    pub(crate) fn insert_node(&self, sdd: &SddRef) {
        self.unique_table.borrow_mut().insert(sdd.id(), sdd.clone());
    }

    pub(crate) fn cache_operation(&self, op: &CachedOperation, result: SddId) {
        match op {
            CachedOperation::BinOp(fst, op, snd) => self.op_cache.borrow_mut().insert(
                Entry {
                    fst: *fst,
                    snd: *snd,
                    op: *op,
                },
                result,
            ),
            CachedOperation::Neg(fst) => self.neg_cache.borrow_mut().insert(*fst, result),
        };
    }

    pub(crate) fn get_cached_operation(&self, op: &CachedOperation) -> Option<SddId> {
        match op {
            CachedOperation::BinOp(fst, op, snd) => self
                .op_cache
                .borrow()
                .get(&Entry {
                    fst: *fst,
                    snd: *snd,
                    op: *op,
                })
                .copied(),
            CachedOperation::Neg(fst) => self.neg_cache.borrow().get(fst).copied(),
        }
    }

    fn get_variables(&self, sdd: &SddRef) -> BTreeSet<Variable> {
        if sdd.is_constant() {
            return BTreeSet::new();
        }

        self.vtree_manager
            .borrow()
            .get_vtree(sdd.vtree().index())
            .unwrap()
            .0
            .borrow()
            .get_variables()
    }

    /// Expand [`models`] with all the possible instantiations of [`unbound _variables`].
    fn expand_models(models: &mut Vec<BitVec>, unbound_variables: &[Variable]) {
        if unbound_variables.is_empty() {
            return;
        }

        let num_models = models.len();
        if unbound_variables.len() == 1 {
            let unbound_variable = unbound_variables.first().unwrap();
            for i in 0..num_models {
                let mut new_model = models.get(i).unwrap().clone();
                new_model.set(unbound_variable.index().0 as usize, true);
                models.push(new_model);
            }

            return;
        }

        for mask in 1..=unbound_variables.len() + 1 {
            let variables_to_set: Vec<_> = set_bits_indices(mask)
                .iter()
                .map(|&idx| unbound_variables.get(idx).unwrap())
                .collect();

            for i in 0..num_models {
                let mut new_model = models.get(i).unwrap().clone();
                for variable_to_set in &variables_to_set {
                    new_model.set(variable_to_set.index().0 as usize, true);
                }
                models.push(new_model);
            }
        }
    }

    pub fn root(&self) -> Option<VTreeRef> {
        self.vtree_manager.borrow().root.clone()
    }

    /// Rotate the vtree [`x`] to the left and adjust SDDs accordingly.
    ///
    /// ```ignore
    ///      w                x
    ///     / \              / \
    ///    a   x     ~>     w   c
    ///       / \          / \
    ///      b   c        a   b
    /// ```
    ///
    /// This is a low-level operation working directly on a vtree. See
    /// [`SddManager::minimization`] for a more sophisticated way of finding better vtrees.
    ///
    /// Children hanged at `w` must be split accordingly, depending on the vtrees
    /// they are normalized for:
    /// * `w(a, bc)` must be rotated and moved to `x` (~> `x(ab, c)`)
    /// * `w(a, c)` must be moved to `x` (~> `x(a, c)`)
    /// * `w(a, b)` stay at `w`
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn rotate_left(&self, x: &VTreeRef) {
        self.rotating.replace(true);

        let w =
            x.0.borrow()
                .get_parent()
                .expect("invalid fragment: `x` does not have a parent");

        let LeftRotateSplit { bc_vec, c_vec } = split_nodes_for_left_rotate(&w, x, self);

        self.vtree_manager.borrow_mut().rotate_left(x);

        for bc in &bc_vec {
            bc.replace_contents(SddType::Decision(Decision {
                elements: rotate_partition_left(bc, x, self).elements,
            }));
            bc.replace_contents(bc.canonicalize(&self).0.borrow().sdd_type.clone());
            bc.set_vtree(x.clone());
        }

        self.finalize_vtree_op(&bc_vec, &c_vec, x);
        self.invalidate_cached_models();

        self.rotating.replace(false);
    }

    fn finalize_vtree_op(&self, replaced: &[SddRef], moved: &[SddRef], vtree: &VTreeRef) {
        for sdd in replaced {
            self.insert_node(sdd);
        }

        for sdd in moved {
            sdd.set_vtree(vtree.clone());
            self.insert_node(sdd);
        }
    }

    /// Rotate the vtree [`x`] to the right and adjust SDDs accordingly.
    ///
    ///
    /// ```ignore
    ///       x                w
    ///      / \              / \
    ///     w   c     ~>     a   x
    ///    / \                  / \
    ///   a   b                b   c
    /// ```
    ///
    /// This is a low-level operation working directly on a vtree. See
    /// [`SddManager::minimization`] for a more sophisticated way of finding better vtrees.
    ///
    /// Children hanged at `w` must be split accordingly, depending on the vtrees
    /// they are normalized for:
    /// * `x(ab, c)` must be rotated and moved to `w` (~> `w(a, bc)`)
    /// * `x(a, c)` must be moved to `w` (~> `w(a, c)`)
    /// * `x(a, b)` stay at `x`
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn rotate_right(&self, x: VTreeRef) {
        self.rotating.replace(true);

        let w = x.left_child();
        let RightRotateSplit { ab_vec, a_vec } = split_nodes_for_right_rotate(&x, &w, self);
        self.vtree_manager.borrow_mut().rotate_right(&x);

        for ab in &ab_vec {
            ab.replace_contents(SddType::Decision(Decision {
                elements: rotate_partition_right(ab, &w, self).elements,
            }));
            ab.replace_contents(ab.canonicalize(&self).0.borrow().sdd_type.clone());

            ab.set_vtree(w.clone());
        }

        self.finalize_vtree_op(&ab_vec, &a_vec, &w);
        self.invalidate_cached_models();

        self.rotating.replace(false);
    }

    /// Swap children of the given vtree [`x`] and adjust SDDs accordingly.
    ///
    /// ```ignore
    ///     x          x
    ///    / \   ~>   / \
    ///   a   b      b   a
    /// ```
    ///
    /// This is a low-level operation working directly on a vtree. See
    /// [`SddManager::minimization`] for a more sophisticated way of finding better vtrees.
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn swap(&self, x: VTreeRef) {
        self.rotating.replace(true);

        let split = split_nodes_for_swap(&x, self);
        self.vtree_manager.borrow_mut().swap(&x);

        for sdd in &split {
            sdd.replace_contents(SddType::Decision(Decision {
                elements: swap_partition(sdd, self).elements,
            }));
            sdd.set_vtree(x.clone());
        }

        self.finalize_vtree_op(&split, &[], &x);
        self.invalidate_cached_models();

        self.rotating.replace(false);
    }

    fn invalidate_cached_models(&self) {
        for (_, sdd) in self.unique_table.borrow().iter() {
            sdd.0.borrow_mut().invalidate_cache();
        }
    }

    pub(crate) fn new_sdd_from_type(
        &self,
        sdd_type: SddType,
        vtree: VTreeRef,
        negation: Option<SddId>,
    ) -> SddRef {
        let sdd = SddRef::new(Sdd::new(sdd_type, *self.next_idx.borrow(), vtree));
        self.move_idx();
        if let Some(negation) = negation {
            self.cache_operation(&CachedOperation::Neg(sdd.id()), negation);
        }

        self.insert_node(&sdd);
        sdd
    }

    fn move_idx(&self) {
        let mut idx = self.next_idx.borrow_mut();
        *idx += SddId(1);
    }
}

#[cfg(test)]
mod test {
    #![allow(non_snake_case)]

    use super::{SddManager, SddOptions};
    use crate::{
        literal::{Literal, Polarity, VariableIdx},
        manager::{
            model::Model,
            options::{GarbageCollection, VTreeStrategy},
        },
    };
    use bon::arr;
    use pretty_assertions::assert_eq;

    #[test]
    fn simple_conjoin() {
        let options = SddOptions::builder().variables(arr!["a", "b"]).build();
        let manager = SddManager::new(&options);

        let tt = manager.tautology();
        let ff = manager.contradiction();

        assert_eq!(tt, manager.conjoin(&tt, &tt));
        assert_eq!(ff, manager.conjoin(&tt, &ff));
        assert_eq!(ff, manager.conjoin(&ff, &tt));
        assert_eq!(ff, manager.conjoin(&ff, &ff));

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_not_a = manager.literal("a", Polarity::Negative);

        assert_eq!(ff, manager.conjoin(&lit_a, &lit_not_a));
        assert_eq!(ff, manager.conjoin(&lit_not_a, &lit_a));
        assert_eq!(lit_a, manager.conjoin(&lit_a, &lit_a));
        assert_eq!(lit_not_a, manager.conjoin(&lit_not_a, &lit_not_a));
    }

    #[test]
    fn simple_disjoin() {
        let options = SddOptions::builder().variables(arr!["a", "b"]).build();
        let manager = SddManager::new(&options);

        let tt = manager.tautology();
        let ff = manager.contradiction();

        assert_eq!(tt, manager.disjoin(&tt, &tt));
        assert_eq!(tt, manager.disjoin(&tt, &ff));
        assert_eq!(tt, manager.disjoin(&ff, &tt));
        assert_eq!(ff, manager.disjoin(&ff, &ff));

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_not_a = manager.literal("a", Polarity::Negative);

        assert_eq!(tt, manager.disjoin(&lit_a, &lit_not_a));
        assert_eq!(tt, manager.disjoin(&lit_not_a, &lit_a));
        assert_eq!(lit_a, manager.disjoin(&lit_a, &lit_a));
        assert_eq!(lit_not_a, manager.disjoin(&lit_not_a, &lit_not_a));
    }

    #[test]
    fn simple_negate() {
        let options = SddOptions::builder().variables(arr!["a", "b"]).build();
        let manager = SddManager::new(&options);

        let tt = manager.tautology();
        let ff = manager.contradiction();

        assert_eq!(ff, manager.negate(&tt));
        assert_eq!(tt, manager.negate(&ff));

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_not_a = manager.literal("a", Polarity::Negative);

        assert_eq!(lit_a, manager.negate(&lit_not_a));
        assert_eq!(lit_not_a, manager.negate(&lit_a));
    }

    #[test]
    fn simple_imply() {
        let options = SddOptions::builder().variables(arr!["a", "b"]).build();
        let manager = SddManager::new(&options);

        let tt = manager.tautology();
        let ff = manager.contradiction();

        assert_eq!(ff, manager.imply(&tt, &ff));
        assert_eq!(tt, manager.imply(&ff, &ff));

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_not_a = manager.literal("a", Polarity::Negative);

        // A => !A <=> !A && !A <=> !A
        assert_eq!(lit_not_a, manager.imply(&lit_a, &lit_not_a));
        // !A => A <=> !!A && A <=> A
        assert_eq!(lit_a, manager.imply(&lit_not_a, &lit_a));
    }

    #[test]
    fn simple_equiv() {
        let options = SddOptions::builder().variables(arr!["a", "b"]).build();
        let manager = SddManager::new(&options);

        let tt = manager.tautology();
        let ff = manager.contradiction();

        assert_eq!(ff, manager.equiv(&tt, &ff));
        assert_eq!(tt, manager.equiv(&ff, &ff));

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_not_a = manager.literal("a", Polarity::Negative);

        assert_eq!(tt, manager.equiv(&lit_a, &lit_a));
        assert_eq!(ff, manager.equiv(&lit_a, &lit_not_a));
    }

    #[test]
    fn apply() {
        let options = SddOptions::builder()
            .variables(arr!["a", "b", "c", "d"])
            .garbage_collection(GarbageCollection::Automatic(0.0))
            .build();
        let manager = SddManager::new(&options);

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        assert_eq!(a_and_d.vtree().index().0, 3);

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d__and_b = manager.conjoin(&a_and_d, &lit_b);
        assert_eq!(a_and_d__and_b.vtree().index().0, 3);
    }

    #[test]
    fn model_counting() {
        let options = SddOptions::builder()
            .variables(arr!["a", "b", "c", "d"])
            .build();
        let manager = SddManager::new(&options);

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        assert_eq!(manager.model_count(&a_and_d), 4);

        let a_or_d = manager.disjoin(&a_and_d, &lit_a);
        assert_eq!(manager.model_count(&a_or_d), manager.model_count(&lit_a));

        let a_and_b = manager.conjoin(&lit_a, &lit_b);
        assert_eq!(manager.model_count(&a_and_b), 4);

        // A && B && B == A && B
        let a_and_b_and_b = manager.conjoin(&a_and_b, &lit_b);
        assert_eq!(
            manager.model_count(&a_and_b_and_b),
            manager.model_count(&a_and_b)
        );

        let a_and_b_and_c = manager.conjoin(&a_and_b, &lit_c);
        assert_eq!(manager.model_count(&a_and_b_and_c), 2);

        let a_and_b_and_c_or_d = manager.disjoin(&a_and_b_and_c, &lit_d);
        assert_eq!(manager.model_count(&a_and_b_and_c_or_d), 9);
    }

    #[test]
    fn model_enumeration() {
        // This test is broken down into two parts since the first
        // part uses only a single literal 'a'.
        {
            let options = SddOptions::builder().variables(arr!["a"]).build();
            let manager = SddManager::new(&options);
            let lit_a = manager.literal("a", Polarity::Positive);

            assert_eq!(
                manager.model_enumeration(&lit_a).all_models(),
                vec![Model::new_from_literals(&[Literal::new(
                    Polarity::Positive,
                    "a",
                    VariableIdx(0)
                )])]
            );
        }

        {
            let options = SddOptions::builder()
                .variables(arr!["a", "b", "c", "d"])
                .build();
            let manager = SddManager::new(&options);
            let lit_a = manager.literal("a", Polarity::Positive);
            let lit_b = manager.literal("b", Polarity::Positive);
            let lit_c = manager.literal("c", Polarity::Positive);
            let lit_d = manager.literal("d", Polarity::Positive);

            let a_and_b = manager.conjoin(&lit_a, &lit_b);
            let models = &[
                Model::new_from_literals(&[
                    Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                    Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                    Literal::new(Polarity::Negative, "c", VariableIdx(2)),
                    Literal::new(Polarity::Negative, "d", VariableIdx(3)),
                ]),
                Model::new_from_literals(&[
                    Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                    Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                    Literal::new(Polarity::Negative, "c", VariableIdx(2)),
                    Literal::new(Polarity::Positive, "d", VariableIdx(3)),
                ]),
                Model::new_from_literals(&[
                    Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                    Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                    Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                    Literal::new(Polarity::Negative, "d", VariableIdx(3)),
                ]),
                Model::new_from_literals(&[
                    Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                    Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                    Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                    Literal::new(Polarity::Positive, "d", VariableIdx(3)),
                ]),
            ];

            assert_eq!(manager.model_enumeration(&a_and_b).all_models(), models);

            let a_and_b_and_c = manager.conjoin(&a_and_b, &lit_c);

            let models = &[
                Model::new_from_literals(&[
                    Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                    Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                    Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                    Literal::new(Polarity::Negative, "d", VariableIdx(3)),
                ]),
                Model::new_from_literals(&[
                    Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                    Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                    Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                    Literal::new(Polarity::Positive, "d", VariableIdx(3)),
                ]),
            ];

            assert_eq!(
                manager.model_enumeration(&a_and_b_and_c).all_models(),
                models
            );

            let a_and_b_and_c_and_d = manager.conjoin(&a_and_b_and_c, &lit_d);
            let models = &[Model::new_from_literals(&[
                Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                Literal::new(Polarity::Positive, "d", VariableIdx(3)),
            ])];
            assert_eq!(
                manager.model_enumeration(&a_and_b_and_c_and_d).all_models(),
                models,
            );

            let not_a = manager.literal("a", Polarity::Negative);
            let ff = manager.conjoin(&not_a, &a_and_b_and_c_and_d);
            assert_eq!(manager.model_enumeration(&ff).all_models(), vec![]);
        }
    }

    #[test]
    fn left_rotation() {
        let options = SddOptions::builder()
            .vtree_strategy(VTreeStrategy::RightLinear)
            .garbage_collection(GarbageCollection::Automatic(0.0))
            .variables(arr!["a", "b", "c", "d"])
            .build();
        let manager = SddManager::new(&options);

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        let a_and_d_and_b = manager.conjoin(&a_and_d, &lit_b);
        let a_and_d_and_b_and_c = manager.conjoin(&a_and_d_and_b, &lit_c);
        let models_before = manager.model_enumeration(&a_and_d_and_b_and_c);

        // Rotating right child of the root to the left makes the vtree balanced.
        manager.rotate_left(&manager.root().unwrap().right_child());

        let models_after = manager.model_enumeration(&a_and_d_and_b_and_c);
        assert_eq!(models_before, models_after);
    }

    #[test]
    fn right_rotation() {
        let options = SddOptions::builder()
            .vtree_strategy(VTreeStrategy::LeftLinear)
            .garbage_collection(GarbageCollection::Automatic(0.0))
            .variables(arr!["a", "b", "c", "d"])
            .build();
        let manager = SddManager::new(&options);

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        let a_and_d_and_b = manager.conjoin(&a_and_d, &lit_b);
        let a_and_d_and_b_and_c = manager.conjoin(&a_and_d_and_b, &lit_c);
        let models_before = manager.model_enumeration(&a_and_d_and_b_and_c);

        // Rotating the root to the right makes the vtree balanced.
        manager.rotate_right(manager.root().unwrap());

        let models_after = manager.model_enumeration(&a_and_d_and_b_and_c);
        assert_eq!(models_before, models_after);
    }

    #[test]
    fn swap() {
        let options = SddOptions::builder()
            .vtree_strategy(VTreeStrategy::Balanced)
            .garbage_collection(GarbageCollection::Automatic(0.0))
            .variables(arr!["a", "b", "c", "d"])
            .build();
        let manager = SddManager::new(&options);

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        let a_and_d_and_b = manager.conjoin(&a_and_d, &lit_b);
        let a_and_d_and_b_and_c = manager.conjoin(&a_and_d_and_b, &lit_c);
        assert_eq!(manager.size(&a_and_d_and_b_and_c), 8);

        let models_before = manager.model_enumeration(&a_and_d_and_b_and_c);

        manager.swap(manager.root().unwrap());

        let models_after = manager.model_enumeration(&a_and_d_and_b_and_c);
        assert_eq!(models_before, models_after);
    }
}
