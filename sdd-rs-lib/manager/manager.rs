use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter},
    literal::{LiteralManager, Polarity, Variable, VariableIdx},
    manager::{dimacs, model::Models, options::SddOptions},
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
    collections::{BTreeSet, HashMap},
    ops::BitOr,
};
use tracing::instrument;

#[derive(Clone, Eq, PartialEq, Hash, Debug, Copy)]
enum Operation {
    Conjoin,
    Disjoin,
}

impl Operation {
    /// Get the absorbing element with respect to the Boolean operation.
    fn zero(&self) -> SddId {
        match self {
            Operation::Conjoin => FALSE_SDD_IDX,
            Operation::Disjoin => TRUE_SDD_IDX,
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug)]
// TODO: Builder pattern with bon?
pub enum TargetVTreeHeuristic {
    TBD,
}

// TODO: Builder pattern with bon?
pub enum CutOff {
    TBD,
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

    next_idx: RefCell<SddId>,
}

// True and false SDDs have indicies 0 and 1 throughout the whole computation.
pub(crate) const FALSE_SDD_IDX: SddId = SddId(0);
pub(crate) const TRUE_SDD_IDX: SddId = SddId(1);

impl SddManager {
    #[must_use]
    pub fn new(options: SddOptions) -> SddManager {
        let mut unique_table = RefCell::new(HashMap::new());
        let ff = SddRef::new(Sdd::new_false());
        let tt = SddRef::new(Sdd::new_true());

        assert_eq!(tt.id(), TRUE_SDD_IDX);
        assert_eq!(ff.id(), FALSE_SDD_IDX);

        unique_table.get_mut().insert(tt.id(), tt);
        unique_table.get_mut().insert(ff.id(), ff);

        SddManager {
            options,
            vtree_manager: RefCell::new(VTreeManager::new()),
            literal_manager: RefCell::new(LiteralManager::new()),
            op_cache: RefCell::new(HashMap::new()),
            next_idx: RefCell::new(SddId(2)), // Account for ff and tt created earlier which have indices 0 and 1.
            unique_table,
        }
    }

    /// Parse a CNF in [DIMACS] format and construct an SDD. Function expects there is a
    /// sufficient number of variables already defined in the manager and tries to map
    /// variable indices in DIMACS to their string representations.
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
        } else if create_variables && preamble.variables > num_variables {
            self.add_remaining_variables(preamble.variables - num_variables);
        }

        let mut sdd = self.tautology();

        loop {
            match dimacs.parse_next_clause().map_err(|err| err.to_string())? {
                None => break,
                Some(clause) => {
                    sdd = self.conjoin(&sdd, &clause.to_sdd(self));
                }
            }
        }

        // TODO: Dimacs output.
        Ok(sdd)
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

    #[must_use]
    pub(crate) fn literal_from_idx(&self, literal: VariableIdx, polarity: Polarity) -> SddRef {
        let (sdd, created) = self.literal_manager.borrow().new_literal_from_idx(
            literal,
            *self.next_idx.borrow(),
            polarity,
            &mut self.vtree_manager.borrow_mut(),
        );

        if created {
            self.move_idx();
        }

        self.insert_node(&sdd);
        sdd
    }

    pub(crate) fn get_nodes_normalized_for(&self, vtree_idx: VTreeIdx) -> Vec<(SddId, SddRef)> {
        self.unique_table
            .borrow()
            .iter()
            .filter(|(_, sdd)| sdd.vtree_idx() == vtree_idx)
            .map(|(id, sdd)| (*id, sdd.clone()))
            .collect()
    }

    pub(crate) fn remove_node(&self, id: SddId) -> std::result::Result<(), ()> {
        tracing::debug!(id = id.0, "removing node from cache");
        let entries: Vec<_> = {
            self.op_cache
                .borrow()
                .iter()
                .filter(|(entry, res)| entry.contains_id(id) || **res == id)
                .map(|(entry, res)| (entry.clone(), *res))
                .collect()
        };

        entries
            .iter()
            .for_each(|(entry, _)| _ = self.op_cache.borrow_mut().remove(entry).unwrap());

        match self.unique_table.borrow_mut().remove(&id) {
            Some(..) => Ok(()),
            None => Err(()),
        }
    }

    pub fn literal(&self, literal: &str, polarity: Polarity) -> SddRef {
        // TODO: Adding new variable should either invalidate cached model counts
        // in existing SDDs or recompute them.
        tracing::warn!("should invalidate cached model counts");

        let (literal, created) = self.literal_manager.borrow().new_literal(
            literal,
            polarity,
            *self.next_idx.borrow(),
            &mut self.vtree_manager.borrow_mut(),
        );

        if created {
            self.move_idx();
        }

        self.insert_node(&literal);
        literal
    }

    pub fn tautology(&self) -> SddRef {
        self.try_get_node(TRUE_SDD_IDX)
            .expect("True SDD node must be present in the unique table at all times")
    }

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
        self.expand_models(&mut models, &unbound_variables);
        Models::new(models, all_variables.iter().cloned().collect())
    }

    pub fn model_count(&self, sdd: &SddRef) -> u64 {
        let models = self._model_count(sdd);

        if self.vtree_manager.borrow().root_idx().unwrap() == sdd.vtree_idx() {
            return models;
        }

        let sdd_variables = self
            .vtree_manager
            .borrow()
            .get_vtree(sdd.vtree_idx())
            .unwrap()
            .0
            .borrow()
            .get_variables()
            .len();
        let unbound = self.literal_manager.borrow().len() - sdd_variables;

        models * 2_u64.pow(unbound as u32)
    }

    // Questions:
    // 1) do we want to trigger minimization only manually?
    //    1a) this seems the easiest to implement if yes
    //    1b) if not, where exactly do we want to trigger it?
    //        1ba) initialize manager with Minimize::AfterApply and after each apply operation,
    //             this would get automatically called.
    //        1bb) initialize manager with Minimize::Automatically and we would minimize during
    //             apply, when computing partitions (this seems the hardest)
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn minimize(
        &self,
        cut_off: CutOff,
        vtree_heuristic: TargetVTreeHeuristic,
        reference_sdd: &SddRef,
    ) {
        // TODO: Remove reference SDD.
        // TODO: Assert that the fragment can be even built.
        // TODO: Strategy for finding better fragment - RandomLeftLinear, RandomRightLinear, Random, original, Custom(VTreeIdx)
        let root = self.vtree_manager.borrow().root.clone().unwrap();
        // Currently, we're constructing just right-linear fragments.
        let rc = root.right_child();

        let mut fragment = Fragment::new(root, rc);

        // TODO: Remove sanity checks.
        let models = self.model_enumeration(reference_sdd);
        tracing::debug!(
            sdd_id = reference_sdd.id().0,
            size = self.size(reference_sdd)
        );

        for i in 0..12 {
            // TODO: Cut off after number of moves, after some time, or if we manage to make the SDD better
            // (=> decrease the number of nodes in the manager).
            fragment.next(&Direction::Forward, self);
            tracing::debug!(
                iteration = i,
                sdd_id = reference_sdd.id().0,
                size = self.size(reference_sdd)
            );
            // TODO: Improve the assertion by doing the first model_enumeration in debug as well.
            debug_assert_eq!(models, self.model_enumeration(reference_sdd));
        }
    }

    /// Get the size of the SDD which is the number of elements reachable from it.
    pub fn size(&self, sdd: &SddRef) -> usize {
        fn traverse_and_count(manager: &SddManager, sdd: &SddRef, seen: &mut Vec<SddId>) -> usize {
            if seen.contains(&sdd.id()) {
                return 0;
            }

            match sdd.0.borrow().sdd_type {
                SddType::Decision(Decision { ref elements }) => {
                    seen.push(sdd.id());

                    elements.len()
                        + elements
                            .iter()
                            .map(|element| element.get_prime_sub(manager))
                            .map(|(prime, sub)| {
                                traverse_and_count(manager, &prime, seen)
                                    + traverse_and_count(manager, &sub, seen)
                            })
                            .sum::<usize>()
                }
                _ => 0,
            }
        }

        let mut seen: Vec<SddId> = Vec::new();
        traverse_and_count(self, sdd, &mut seen)
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
                panic!(
                    "every other sddType should've been handled ({:?})",
                    sdd_type
                );
            };

            let all_variables = self.get_variables(sdd);
            for Element { prime, sub } in &decision.elements {
                let mut models = Vec::new();
                let prime = self.get_node(*prime);
                let sub = self.get_node(*sub);

                if prime.is_false() || sub.is_false() {
                    continue;
                }

                if prime.is_true() || sub.is_true() {
                    if prime.is_true() {
                        self._model_enumeration(&sub, &mut models);
                    } else {
                        self._model_enumeration(&prime, &mut models);
                    }
                } else {
                    let mut fst = Vec::new();
                    let mut snd = Vec::new();

                    self._model_enumeration(&prime, &mut fst);
                    self._model_enumeration(&sub, &mut snd);

                    for fst_bv in &fst {
                        for snd_bv in &snd {
                            models.push(fst_bv.clone().bitor(snd_bv));
                        }
                    }
                }

                let all_reachable_variables = self
                    .get_variables(&prime)
                    .union(&self.get_variables(&sub))
                    .cloned()
                    .collect();
                let unbound_variables: Vec<_> = all_variables
                    .difference(&all_reachable_variables)
                    .cloned()
                    .collect();

                self.expand_models(&mut models, &unbound_variables);
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
                if sdd.is_literal() {
                    1
                } else {
                    self._model_count(sdd)
                }
            };

            let all_variables = self.get_variables(sdd).len();

            for Element { prime, sub } in &decision.elements {
                let prime = self.get_node(*prime);
                let sub = self.get_node(*sub);

                let model_count = get_models_count(&prime) * get_models_count(&sub);

                // Account for variables that do not appear in neither prime or sub.
                let all_reachable = self
                    .get_variables(&prime)
                    .union(&self.get_variables(&sub))
                    .count();
                let unbound_variables = all_variables - all_reachable;

                total_models += model_count * 2_u64.pow(unbound_variables as u32);
            }
        }

        sdd.cache_model_count(total_models);
        total_models
    }

    pub fn draw_all_sdds(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("sdd"), true);
        for node in self.unique_table.borrow().values() {
            node.0.borrow().draw(&mut dot_writer, self);
        }
        dot_writer.write(writer)
    }

    pub fn draw_sdd(&self, writer: &mut dyn std::io::Write, sdd: &SddRef) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("sdd"), true);

        let mut sdds = vec![sdd.clone()];
        while let Some(sdd) = sdds.pop() {
            sdd.0.borrow().draw(&mut dot_writer, self);

            if let SddType::Decision(Decision { ref elements }) = sdd.0.borrow().sdd_type {
                elements
                    .iter()
                    .map(|element| element.get_prime_sub(self))
                    .for_each(|(prime, sub)| {
                        sdds.push(prime);
                        sdds.push(sub)
                    });
            };
        }

        dot_writer.write(writer)
    }

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_vtree_graph(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("vtree"), false);
        self.vtree_manager.borrow().draw(&mut dot_writer, self);
        dot_writer.write(writer)
    }

    /// Apply operation on the two Sdds.
    #[must_use]
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn apply(&self, fst: &SddRef, snd: &SddRef, op: Operation) -> SddRef {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "apply");
        let (fst, snd) = if fst.vtree_idx() < snd.vtree_idx() {
            (fst, snd)
        } else {
            (snd, fst)
        };

        if let Some(result_id) = self.op_cache.borrow().get(&Entry {
            fst: fst.id(),
            snd: snd.id(),
            op,
        }) {
            tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "cached");
            return self.get_node(*result_id);
        }

        let (lca, order) = self
            .vtree_manager
            .borrow()
            .least_common_ancestor(fst.vtree_idx(), snd.vtree_idx());

        let elements = match order {
            VTreeOrder::Equal => self._apply_eq(fst, snd, op),
            VTreeOrder::Inequal => self._apply_ineq(fst, snd, op),
            VTreeOrder::LeftSubOfRight => self._apply_left_sub_of_right(fst, snd, op),
            VTreeOrder::RightSubOfLeft => self._apply_right_sub_of_left(fst, snd, op),
        };

        let sdd = Sdd::unique_d(elements.clone(), lca.index(), self);
        sdd.canonicalize(self);
        // TODO: canonicalize is not working properly => infinite loop since it's not changing.

        self.insert_node(&sdd);
        self.cache_operation(fst.id(), snd.id(), op, sdd.id());

        // TODO: Show where the properties are violated.
        debug_assert!(sdd.is_trimmed(self));
        debug_assert!(sdd.is_compressed(self));

        sdd
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn _apply_eq(&self, fst: &SddRef, snd: &SddRef, op: Operation) -> BTreeSet<Element> {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "apply_eq");
        assert_eq!(fst.vtree_idx(), snd.vtree_idx());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let mut elements = BTreeSet::new();
        for Element {
            prime: fst_prime,
            sub: fst_sub,
        } in fst.0.borrow().expand().elements.iter()
        {
            for Element {
                prime: snd_prime,
                sub: snd_sub,
            } in snd.0.borrow().expand().elements.iter()
            {
                let fst_prime = self.get_node(*fst_prime);
                let snd_prime = self.get_node(*snd_prime);
                let res_prime = self.conjoin(&fst_prime, &snd_prime);

                if !res_prime.is_false() {
                    let fst_sub = &self.get_node(*fst_sub);
                    let snd_sub = &self.get_node(*snd_sub);
                    let res_sub = match op {
                        Operation::Conjoin => self.disjoin(fst_sub, snd_sub),
                        Operation::Disjoin => self.conjoin(fst_sub, snd_sub),
                    };

                    if res_sub.is_true() && res_prime.is_true() {
                        println!(
                            "_apply_eq: we can optimize since res_sub and res_prime are both true"
                        )
                    }

                    elements.insert(Element {
                        prime: res_prime.id(),
                        sub: res_sub.id(),
                    });
                }
            }
        }

        elements
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    fn _apply_ineq(&self, fst: &SddRef, snd: &SddRef, op: Operation) -> BTreeSet<Element> {
        tracing::debug!(fst_id = fst.id().0, snd_id = snd.id().0, ?op, "apply_ineq");
        assert!(fst.vtree_idx() < snd.vtree_idx());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let fst_negated = fst.clone().negate(self);

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
                prime: fst.id(),
                sub: apply(snd, &tt).id(),
            },
            Element {
                prime: fst_negated.id(),
                sub: apply(snd, &ff).id(),
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

        if let Some(result_id) = self.op_cache.borrow().get(&Entry {
            fst: fst.id(),
            snd: snd.id(),
            op: Operation::Conjoin,
        }) {
            return self.get_node(*result_id);
        }

        let elements = btreeset!(
            Element {
                prime: fst.id(),
                sub: snd.id(),
            },
            Element {
                prime: self.negate(&fst).id(),
                sub: FALSE_SDD_IDX
            }
        );

        let sdd = Sdd::unique_d(elements, lca.index(), self);
        sdd.canonicalize(self);

        self.insert_node(&sdd);
        self.cache_operation(fst.id(), snd.id(), Operation::Conjoin, sdd.id());

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
        assert!(fst.vtree_idx() < snd.vtree_idx());
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let new_node = if op == Operation::Conjoin {
            fst
        } else {
            &fst.clone().negate(self)
        };

        let snd_elements = snd.0.borrow().sdd_type.elements().unwrap_or_else(||
            panic!(
                "snd of _apply_left_sub_of_right must be a decision node but was instead {} (id {})",
                snd.0.borrow().sdd_type.name(),
                snd.id(),
            )
        );

        let mut elements = btreeset!(Element {
            prime: self.negate(new_node).id(),
            sub: op.zero(),
        });

        for Element {
            prime: snd_prime,
            sub: snd_sub,
        } in snd_elements
        {
            let snd_prime = self.get_node(snd_prime);
            let new_prime = self.conjoin(&snd_prime, new_node);
            if !new_prime.is_false() {
                elements.insert(Element {
                    prime: new_prime.id(),
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
        assert!(fst.vtree_idx() < snd.vtree_idx());
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
            prime: fst_prime_idx,
            sub: fst_sub_idx,
        } in fst_elements
        {
            let fst_sub = self.get_node(fst_sub_idx);
            let new_sub = match op {
                Operation::Conjoin => self.conjoin(&fst_sub, snd),
                Operation::Disjoin => self.disjoin(&fst_sub, snd),
            };

            elements.insert(Element {
                prime: fst_prime_idx,
                sub: new_sub.id(),
            });
        }

        elements
    }
    // TODO: expose operations manipulating the vtree.

    pub(crate) fn insert_node(&self, sdd: &SddRef) {
        self.unique_table.borrow_mut().insert(sdd.id(), sdd.clone());
    }

    #[instrument]
    fn cache_operation(&self, fst: SddId, snd: SddId, op: Operation, res_id: SddId) {
        self.op_cache
            .borrow_mut()
            .insert(Entry { fst, snd, op }, res_id);
    }

    fn get_variables(&self, sdd: &SddRef) -> BTreeSet<Variable> {
        if sdd.is_constant() {
            return BTreeSet::new();
        }

        self.vtree_manager
            .borrow()
            .get_vtree(sdd.vtree_idx())
            .unwrap()
            .0
            .borrow()
            .get_variables()
    }

    /// Expand [`models`] with all the possible instantiations of [`unbound _variables`].
    fn expand_models(&self, models: &mut Vec<BitVec>, unbound_variables: &[Variable]) {
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

    /// Generate labels for remaining variables to be added to the label_manager
    /// and adjust the vtree accordingly.
    fn add_remaining_variables(&self, to_add: usize) {
        fn variable_exists(manager: &SddManager, variable: &Variable) -> bool {
            manager.literal_manager.borrow().exists(variable)
        }

        fn next_variable_idx(manager: &SddManager) -> u32 {
            manager.literal_manager.borrow().len() as u32
        }

        let alphabet = String::from_utf8((b'A'..=b'Z').collect()).unwrap();
        let mut i = 0;
        let mut to_add = to_add;
        while i < to_add {
            let generation = i / 26;
            let idx = i % 26;

            let next_idx = next_variable_idx(self);
            let var_repr = format!("{}_{generation}", alphabet.get(idx..idx + 1).unwrap());
            let variable = Variable::new(&var_repr, next_idx);
            if !variable_exists(self, &variable) {
                // "Take advantage" of the `literal` method which correctly inserts the variable
                // and adjusts the vtree.
                self.literal(&var_repr, Polarity::Positive);
            } else {
                // Move to_add to try the next variable.
                to_add += 1;
            }
            i += 1;
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
        let w =
            x.0.borrow()
                .get_parent()
                .expect("invalid fragment: `x` does not have a parent");

        self.vtree_manager.borrow_mut().rotate_left(x);

        // TODO: Check that caches are correct (unique_table, op_cache, model_count and models).
        let LeftRotateSplit { bc_vec, c_vec } = split_nodes_for_left_rotate(&w, x, self);

        for bc in &bc_vec {
            bc.set_vtree_idx(x.index());
            let decision = SddType::Decision(Decision {
                elements: rotate_partition_left(bc, x, self).elements,
            });

            bc.replace_contents(decision);
            self.insert_node(bc);
        }

        self.finalize_vtree_op(&bc_vec, &c_vec, &x);

        // TODO: Make sure this is actually needed.
        self.invalidate_cached_models();
    }

    fn finalize_vtree_op(&self, replaced: &[SddRef], moved: &[SddRef], vtree: &VTreeRef) {
        for sdd in replaced {
            self.insert_node(&sdd);
        }

        for sdd in moved {
            sdd.set_vtree_idx(vtree.index());
            self.insert_node(&sdd);
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
    /// * `x(a, c)` must be moved to `w` (~> `x(a, c)`)
    /// * `x(a, b)` stay at `x`
    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub fn rotate_right(&self, x: &VTreeRef) {
        // TODO: Double check all the vtree occurances.
        // TODO: Double check computing the cartesian product.
        let w = x.left_child();

        self.vtree_manager.borrow_mut().rotate_right(x);

        // TODO: Check that caches are correct (unique_table, op_cache, model_count and models).
        let RightRotateSplit { ab_vec, a_vec } = split_nodes_for_right_rotate(x, &w, self);

        for ab in &ab_vec {
            ab.replace_contents(SddType::Decision(Decision {
                elements: rotate_partition_right(ab, &w, self).elements,
            }));
            ab.set_vtree_idx(w.index());
            self.insert_node(ab);
        }

        self.finalize_vtree_op(&ab_vec, &a_vec, &w);

        // TODO: Make sure this is actually needed.
        self.invalidate_cached_models();
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
    pub fn swap(&self, x: &VTreeRef) {
        let split = split_nodes_for_swap(x, self);

        self.vtree_manager.borrow_mut().swap(x);

        for sdd in &split {
            sdd.replace_contents(SddType::Decision(Decision {
                elements: swap_partition(sdd, x, self).elements,
            }));
            sdd.set_vtree_idx(x.index());
            self.insert_node(sdd);
        }

        // TODO: Make sure this is actually needed.
        self.invalidate_cached_models();
    }

    fn invalidate_cached_models(&self) {
        for (_, sdd) in self.unique_table.borrow().iter() {
            sdd.0.borrow_mut().invalidate_cache();
        }
    }

    pub(crate) fn new_sdd_from_type(
        &self,
        sdd_type: SddType,
        vtree_idx: VTreeIdx,
        negation: Option<SddId>,
    ) -> SddRef {
        let sdd = SddRef::new(Sdd::new(
            sdd_type,
            *self.next_idx.borrow(),
            vtree_idx,
            negation,
        ));
        self.move_idx();

        self.insert_node(&sdd);
        sdd
    }

    pub(crate) fn new_sdd(&self, sdd: Sdd) -> SddRef {
        let mut sdd = sdd.clone();
        sdd.sdd_idx = *self.next_idx.borrow();

        let sdd = SddRef::new(sdd);
        self.insert_node(&sdd);

        self.move_idx();

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
        manager::model::Model,
        util::quick_draw,
    };
    use pretty_assertions::assert_eq;

    #[test]
    fn simple_conjoin() {
        let manager = SddManager::new(SddOptions::default());

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
        let manager = SddManager::new(SddOptions::default());

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
        let manager = SddManager::new(SddOptions::default());

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
        let manager = SddManager::new(SddOptions::default());

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
        let manager = SddManager::new(SddOptions::default());

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
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let _ = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        // Rotate the right child of root to the left to make the tree balanced as in the diagram above.
        let root = manager.vtree_manager.borrow().root.clone().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&root.right_child());

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        assert_eq!(a_and_d.vtree_idx().0, 3);

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d__and_b = manager.conjoin(&a_and_d, &lit_b);
        assert_eq!(a_and_d__and_b.vtree_idx().0, 3);
    }

    #[test]
    fn model_counting() {
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        // Make the vtree balanced.
        let root = manager.vtree_manager.borrow().root.clone().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&root.right_child());

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
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);

        assert_eq!(
            manager.model_enumeration(&lit_a).all_models(),
            vec![Model::new_from_literals(vec![Literal::new(
                Polarity::Positive,
                "a",
                VariableIdx(0)
            )])]
        );

        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let root = manager.vtree_manager.borrow().root.clone().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&root.right_child());

        let a_and_b = manager.conjoin(&lit_a, &lit_b);
        let models = vec![
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                Literal::new(Polarity::Negative, "c", VariableIdx(2)),
                Literal::new(Polarity::Negative, "d", VariableIdx(3)),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                Literal::new(Polarity::Negative, "c", VariableIdx(2)),
                Literal::new(Polarity::Positive, "d", VariableIdx(3)),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                Literal::new(Polarity::Negative, "d", VariableIdx(3)),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                Literal::new(Polarity::Positive, "d", VariableIdx(3)),
            ]),
        ];

        assert_eq!(manager.model_enumeration(&a_and_b).all_models(), models);

        let a_and_b_and_c = manager.conjoin(&a_and_b, &lit_c);
        let models = vec![
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", VariableIdx(0)),
                Literal::new(Polarity::Positive, "b", VariableIdx(1)),
                Literal::new(Polarity::Positive, "c", VariableIdx(2)),
                Literal::new(Polarity::Negative, "d", VariableIdx(3)),
            ]),
            Model::new_from_literals(vec![
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
        let models = vec![Model::new_from_literals(vec![
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

    #[test]
    fn left_rotation() {
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        // Rotate the right child of root to the left to make the tree balanced as in the diagram above.
        let root = manager.root().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&root.right_child());

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        let a_and_d_and_b = manager.conjoin(&a_and_d, &lit_b);
        let a_and_d_and_b_and_c = manager.conjoin(&a_and_d_and_b, &lit_c);
        let models_before = manager.model_enumeration(&a_and_d_and_b_and_c);

        manager.rotate_left(&manager.root().unwrap().right_child());

        let models_after = manager.model_enumeration(&a_and_d_and_b_and_c);
        assert_eq!(models_before, models_after);
    }

    #[test]
    fn right_rotation() {
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        // Rotate the right child of root to the left to make the tree balanced as in the diagram above.
        let root = manager.root().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&root.right_child());

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        let a_and_d_and_b = manager.conjoin(&a_and_d, &lit_b);
        let a_and_d_and_b_and_c = manager.conjoin(&a_and_d_and_b, &lit_c);
        let models_before = manager.model_enumeration(&a_and_d_and_b_and_c);

        manager.rotate_right(&manager.root().unwrap());

        let models_after = manager.model_enumeration(&a_and_d_and_b_and_c);
        assert_eq!(models_before, models_after);
    }

    #[test]
    fn swap() {
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        // Rotate the right child of root to the left to make the tree balanced as in the diagram above.
        let root = manager.root().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&root.right_child());

        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        let a_and_d_and_b = manager.conjoin(&a_and_d, &lit_b);
        let a_and_d_and_b_and_c = manager.conjoin(&a_and_d_and_b, &lit_c);
        assert_eq!(manager.size(&a_and_d_and_b_and_c), 8);

        let models_before = manager.model_enumeration(&a_and_d_and_b_and_c);

        manager.swap(&manager.root().unwrap());

        let models_after = manager.model_enumeration(&a_and_d_and_b_and_c);
        assert_eq!(models_before, models_after);
    }
}
