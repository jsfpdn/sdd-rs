use bitvec::prelude::*;

use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter},
    literal::{Literal, Polarity, Variable},
    manager::{dimacs, model::Models, options::SddOptions},
    sdd::{Decision, Element, Sdd, SddType},
    util::set_bits_indices,
    vtree::{VTreeManager, VTreeOrder},
};

use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
    ops::BitOr,
};

#[derive(Clone, Eq, PartialEq, Hash, Debug, Copy)]
enum Operation {
    Conjoin,
    Disjoin,
}

impl Operation {
    /// Get the absorbing element with respect to the Boolean operation.
    fn zero(&self) -> Sdd {
        match self {
            Operation::Conjoin => Sdd::new_false(),
            Operation::Disjoin => Sdd::new_true(),
        }
    }
}

#[derive(Eq, PartialEq, Hash)]
struct Entry {
    fst: usize,
    snd: usize,
    op: Operation,
}

#[allow(clippy::module_name_repetitions)]
pub struct SddManager {
    options: SddOptions,

    vtree_manager: RefCell<VTreeManager>,
    label_manager: RefCell<BTreeSet<Variable>>,

    // Unique table holding all the decision nodes.
    // More details can be found in [Algorithms and Data Structures in VLSI Design](https://link.springer.com/book/10.1007/978-3-642-58940-9).
    unique_table: RefCell<HashMap<usize, Sdd>>,

    // Caches all the computations.
    op_cache: RefCell<HashMap<Entry, usize>>,
}

impl SddManager {
    #[must_use]
    pub fn new(options: SddOptions) -> SddManager {
        let mut unique_table = RefCell::new(HashMap::new());
        unique_table
            .get_mut()
            .insert(Sdd::new_true().id(), Sdd::new_true());
        unique_table
            .get_mut()
            .insert(Sdd::new_false().id(), Sdd::new_false());

        SddManager {
            options,
            vtree_manager: RefCell::new(VTreeManager::new()),
            label_manager: RefCell::new(BTreeSet::new()),
            op_cache: RefCell::new(HashMap::new()),
            unique_table,
        }
    }

    // TODO: function to "dynamically" create alphabetical variables from a given range.

    /// Parse a CNF in [DIMACS] format and construct an SDD. Function expects there is a
    /// sufficient number of variables already defined in the manager and tries to map
    /// variable indices in DIMACS to their string representations.
    ///
    /// [DIMACS]: https://www21.in.tum.de/~lammich/2015_SS_Seminar_SAT/resources/dimacs-cnf.pdf
    pub fn from_dimacs(&self, reader: &mut dyn std::io::Read) -> Result<Sdd, String> {
        // TODO: Timing

        let mut reader = std::io::BufReader::new(reader);
        let mut dimacs = dimacs::DimacsReader::new(&mut reader);

        let preamble = dimacs.parse_preamble().map_err(|err| err.to_string())?;
        if preamble.variables > self.label_manager.borrow().len() {
            return Err(String::from(
                "preamble specifies more variables than those present in the manager",
            ));
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

    // TODO: This function should be removed as user should not be able to fill the unique_table
    // directly.
    #[must_use]
    pub(crate) fn new_with_nodes(options: SddOptions, sdds: &[Sdd]) -> SddManager {
        let mut table = HashMap::new();
        let mut vars = BTreeSet::new();
        for sdd in sdds {
            table.insert(sdd.id(), sdd.clone());

            match &sdd.sdd_type {
                SddType::Literal(literal) => {
                    _ = vars.insert(literal.clone().var_label());
                }
                _ => {}
            };
        }
        table.insert(Sdd::new_true().id(), Sdd::new_true());
        table.insert(Sdd::new_false().id(), Sdd::new_false());

        SddManager {
            options,
            vtree_manager: RefCell::new(VTreeManager::new()),
            label_manager: RefCell::new(vars),
            unique_table: RefCell::new(table),
            op_cache: RefCell::new(HashMap::new()),
        }
    }

    /// # Panics
    /// Function panics if there is no such node with the corresponding id in the unique table.
    #[must_use]
    pub(crate) fn get_node(&self, id: usize) -> Option<Sdd> {
        self.unique_table.borrow().get(&id).map(|n| n.clone())
    }

    #[must_use]
    pub(crate) fn literal_from_idx(&self, literal: u16, polarity: Polarity) -> Sdd {
        let label = self
            .label_manager
            .borrow()
            .iter()
            .find(|variable| variable.index() == literal)
            .cloned()
            .unwrap();

        self.literal(&label.label(), polarity)
    }

    pub fn literal(&self, literal: &str, polarity: Polarity) -> Sdd {
        let variable = self
            .label_manager
            .borrow()
            .iter()
            .find(|variable| variable.label() == literal)
            .cloned();
        let variable = variable.unwrap_or_else(|| {
            let variable = Variable::new(literal, self.label_manager.borrow().len() as u16);
            self.vtree_manager.borrow_mut().add_variable(&variable);
            self.label_manager.borrow_mut().insert(variable.clone());
            variable
        });

        // TODO: Adding new variable should either invalidate cached model counts
        // in existing SDDs or recompute them.
        // warn!("should invalidate cached model counts");

        let vtree_idx = self
            .vtree_manager
            .borrow()
            .get_variable_vtree(&variable)
            .expect("var_label was just inserted, therefore it must be present and found")
            .borrow()
            .get_index();

        let literal = Sdd::new(
            SddType::Literal(Literal::new_with_label(polarity, variable.clone())),
            vtree_idx,
            None,
        );

        self.insert_node(&literal);
        literal
    }

    pub fn tautology(&self) -> Sdd {
        Sdd::new_true()
    }

    pub fn contradiction(&self) -> Sdd {
        Sdd::new_false()
    }

    #[must_use]
    pub fn conjoin(&self, fst: &Sdd, snd: &Sdd) -> Sdd {
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
    pub fn disjoin(&self, fst: &Sdd, snd: &Sdd) -> Sdd {
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
    pub fn negate(&self, fst: &Sdd) -> Sdd {
        fst.clone().negate(self)
    }

    #[must_use]
    pub fn imply(&self, fst: &Sdd, snd: &Sdd) -> Sdd {
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
        self.apply(&fst.clone().negate(self), snd, Operation::Disjoin)
    }

    #[must_use]
    pub fn equiv(&self, fst: &Sdd, snd: &Sdd) -> Sdd {
        if fst == snd {
            return self.tautology();
        }

        if fst.eq_negated(snd, self) {
            return self.contradiction();
        }

        // Relies on the fact that A <=> B is equivalent (!A && !B) || (A && B).
        let fst_con = &self.conjoin(&fst.clone().negate(self), &snd.clone().negate(self));
        let snd_con = &self.conjoin(fst, snd);
        self.disjoin(fst_con, snd_con)
    }

    /// Condition an SDD on a literal.
    pub fn condition(&self, literal: &Literal, sdd: &Sdd) -> Sdd {
        // TODO: Improve construction of literals to be passed here since from user's POV
        // they are just SDDs, since we want to levarage type system.
        unimplemented!()
    }

    pub fn exist() {}
    pub fn forall() {}

    /// Enumerate all models of the SDD. This method eagerly computes all satisfying assignments.
    pub fn model_enumeration(&self, sdd: &Sdd) -> Models {
        let mut models: Vec<BitVec> = Vec::new();
        self._model_enumeration(sdd, &mut models);

        let all_variables: BTreeSet<_> = self.label_manager.borrow().iter().cloned().collect();
        let unbound_variables: Vec<_> = all_variables
            .difference(&self.get_variables(&sdd))
            .cloned()
            .collect();
        self.expand_models(&mut models, &unbound_variables);
        Models::new(models, all_variables.iter().cloned().collect())
    }

    fn _model_enumeration(&self, sdd: &Sdd, bitvecs: &mut Vec<BitVec>) {
        // Return the cached value if it already exists.
        if let Some(ref mut models) = sdd.models.clone() {
            bitvecs.append(models);
            return;
        }

        // This is "hack" due to the very design of this lib. We may have computed
        // the model count already but it's not visible in the Sdd reference. It should
        // be in the unique table though, if it was in fact computed.
        if let Some(ref mut models) = self.get_node(sdd.id()).unwrap().models.clone() {
            bitvecs.append(models);
            return;
        }

        if let SddType::Literal(ref literal) = sdd.sdd_type {
            let mut model = bitvec![usize, LocalBits; 0; self.label_manager.borrow().len()];
            model.set(
                literal.var_label().index() as usize,
                literal.polarity() == Polarity::Positive,
            );
            bitvecs.push(model);
            return;
        }

        let SddType::Decision(decision) = sdd.sdd_type.clone() else {
            panic!(
                "every other sddType should've been handled ({:?})",
                sdd.sdd_type
            );
        };

        let mut all_models = Vec::new();
        let all_variables = self.get_variables(&sdd);

        for Element { prime, sub } in decision.elements {
            let mut models = Vec::new();
            let prime = self.get_node(prime).unwrap();
            let sub = self.get_node(sub).unwrap();

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

        bitvecs.append(&mut all_models);

        let mut sdd_clone = sdd.clone();
        sdd_clone.models = Some(bitvecs.clone());
        self.insert_node(&sdd_clone);
    }

    pub fn model_count(&self, sdd: &Sdd) -> u64 {
        let models = self._model_count(sdd);

        if self.vtree_manager.borrow().root_idx().unwrap() == sdd.vtree_idx {
            return models;
        }

        let sdd_variables = self
            .vtree_manager
            .borrow()
            .get_vtree(sdd.vtree_idx)
            .unwrap()
            .borrow()
            .get_variables()
            .len();
        let unbound = self.label_manager.borrow().len() - sdd_variables;

        models * 2_u64.pow(unbound as u32)
    }

    /// Count number of models for this SDD.
    fn _model_count(&self, sdd: &Sdd) -> u64 {
        // Return the cached value if it already exists.
        if let Some(model_count) = sdd.model_count {
            return model_count;
        }

        // This is "hack" due to the very design of this lib. We may have computed
        // the model count already but it's not visible in the Sdd reference. It should
        // be in the unique table though, if it was in fact computed.
        if let Some(model_count) = self.get_node(sdd.id()).unwrap().model_count {
            return model_count;
        }

        let SddType::Decision(decision) = sdd.sdd_type.clone() else {
            panic!("every other sddType should've been handled");
        };

        let get_models_count = |sdd: &Sdd| {
            if sdd.is_literal() {
                1
            } else {
                self._model_count(sdd)
            }
        };

        let mut total_models = 0;
        let all_variables = self.get_variables(&sdd).len();

        for Element { prime, sub } in decision.elements {
            let prime = self.get_node(prime).unwrap();
            let sub = self.get_node(sub).unwrap();

            let model_count = get_models_count(&prime) * get_models_count(&sub);

            // Account for variables that do not appear in neither prime or sub.
            let all_reachable = self
                .get_variables(&prime)
                .union(&self.get_variables(&sub))
                .count();
            let unbound_variables = all_variables - all_reachable;

            total_models += model_count * 2_u64.pow(unbound_variables as u32);
        }

        // Update the "global" sdd in the unique table so we can find it later.
        let mut sdd_clone = sdd.clone();
        sdd_clone.model_count = Some(total_models);
        self.insert_node(&sdd_clone);

        total_models
    }

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_all_sdds<'b>(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("sdd"), true);
        for node in self.unique_table.borrow().values() {
            node.draw(&mut dot_writer, self);
        }
        dot_writer.write(writer)
    }

    pub fn draw_sdd(&self, writer: &mut dyn std::io::Write, sdd: &Sdd) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("sdd"), true);

        let mut sdds = vec![sdd.clone()];
        while !sdds.is_empty() {
            let sdd = sdds.pop().unwrap();
            sdd.draw(&mut dot_writer, self);

            if let SddType::Decision(Decision { elements }) = sdd.sdd_type.clone() {
                elements
                    .iter()
                    .map(|element| element.get_prime_sub(self))
                    .for_each(|(prime, sub)| {
                        sdds.push(prime);
                        sdds.push(sub)
                    });
            }
        }

        dot_writer.write(writer)
    }

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_vtree_graph<'b>(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        let mut dot_writer = DotWriter::new(String::from("vtree"), false);
        self.vtree_manager.borrow().draw(&mut dot_writer, self);
        dot_writer.write(writer)
    }

    /// Apply operation on the two Sdds.
    #[must_use]
    fn apply(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> Sdd {
        let (fst, snd) = if fst.vtree_idx < snd.vtree_idx {
            (fst, snd)
        } else {
            (snd, fst)
        };

        if let Some(result_id) = self.op_cache.borrow().get(&Entry {
            fst: fst.id(),
            snd: snd.id(),
            op: op.clone(),
        }) {
            return self
                .get_node(*result_id)
                .expect("Node is missing in the unique_table!")
                .clone();
        }

        let (lca, order) = self
            .vtree_manager
            .borrow()
            .least_common_ancestor(fst.vtree_idx, snd.vtree_idx);

        let elements = match order {
            VTreeOrder::Equal => self._apply_eq(fst, snd, op),
            VTreeOrder::Inequal => self._apply_ineq(fst, snd, op),
            VTreeOrder::LeftSubOfRight => self._apply_left_sub_of_right(fst, snd, op),
            VTreeOrder::RightSubOfLeft => self._apply_right_sub_of_left(fst, snd, op),
        };

        let sdd = Sdd::unique_d(elements, lca.borrow().get_index()).canonicalize(self);

        self.insert_node(&sdd);
        self.cache_operation(fst.id(), snd.id(), op, sdd.id());

        // TODO: Show where the properties are violated.
        debug_assert!(sdd.is_trimmed(self));
        debug_assert!(sdd.is_compressed(self));

        sdd
    }

    fn _apply_eq(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> BTreeSet<Element> {
        assert_eq!(fst.vtree_idx, snd.vtree_idx);
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let mut elements = BTreeSet::new();
        for Element {
            prime: fst_prime,
            sub: fst_sub,
        } in fst.expand().elements.iter()
        {
            for Element {
                prime: snd_prime,
                sub: snd_sub,
            } in snd.expand().elements.iter()
            {
                let fst_prime = self.get_node(*fst_prime).unwrap();
                let snd_prime = self.get_node(*snd_prime).unwrap();
                let res_prime = self.conjoin(&fst_prime, &snd_prime);

                if !res_prime.is_false() {
                    let fst_sub = &self.get_node(*fst_sub).unwrap();
                    let snd_sub = &self.get_node(*snd_sub).unwrap();
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

    fn _apply_ineq(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> BTreeSet<Element> {
        assert!(fst.vtree_idx < snd.vtree_idx);
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let fst_negated = fst.clone().negate(self);

        let apply = |fst, snd| {
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

    fn _apply_left_sub_of_right(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> BTreeSet<Element> {
        assert!(fst.vtree_idx < snd.vtree_idx);
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let new_node = if op == Operation::Conjoin {
            fst
        } else {
            &fst.clone().negate(self)
        };

        let snd_elements = snd.sdd_type.elements().expect(
            format!(
                "snd of _apply_left_sub_of_right must be a decision node but was instead {} (id {})",
                snd.sdd_type.name(),
                snd.id(),
            ).as_str()
        );

        let mut elements = btreeset!(Element {
            prime: new_node.clone().negate(self).id(),
            sub: op.zero().id(),
        });

        for Element {
            prime: snd_prime,
            sub: snd_sub,
        } in snd_elements
        {
            let snd_prime = &self.get_node(snd_prime).unwrap();
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

    fn _apply_right_sub_of_left(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> BTreeSet<Element> {
        assert!(fst.vtree_idx < snd.vtree_idx);
        assert!(!fst.is_constant());
        assert!(!snd.is_constant());

        let fst_elements = fst.sdd_type.elements().expect(
            format!(
                "snd of _apply_right_sub_of_left must be a decision node but was instead {} (id {})",
                snd.sdd_type.name(),
                snd.id(),
            )
            .as_str(),
        );

        let mut elements = BTreeSet::new();

        for Element {
            prime: fst_prime_idx,
            sub: fst_sub_idx,
        } in fst_elements
        {
            let fst_sub = self.get_node(fst_sub_idx).unwrap();
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

    pub(crate) fn insert_node(&self, sdd: &Sdd) {
        self.unique_table.borrow_mut().insert(sdd.id(), sdd.clone());
    }

    fn cache_operation(&self, fst: usize, snd: usize, op: Operation, res_id: usize) {
        self.op_cache
            .borrow_mut()
            .insert(Entry { fst, snd, op }, res_id);
    }

    fn get_variables(&self, sdd: &Sdd) -> BTreeSet<Variable> {
        if sdd.is_constant() {
            return BTreeSet::new();
        }

        self.vtree_manager
            .borrow()
            .get_vtree(sdd.vtree_idx)
            .unwrap()
            .borrow()
            .get_variables()
    }

    /// Expand [`models`] with all the possible instantiations of [`unbound _variables`].
    fn expand_models(&self, models: &mut Vec<BitVec>, unbound_variables: &[Variable]) {
        if unbound_variables.len() == 0 {
            return;
        }

        let num_models = models.len();
        if unbound_variables.len() == 1 {
            let unbound_variable = unbound_variables.get(0).unwrap();
            for i in 0..num_models {
                let mut new_model = models.get(i).unwrap().clone();
                new_model.set(unbound_variable.index() as usize, true);
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
                    new_model.set(variable_to_set.index() as usize, true);
                }
                models.push(new_model);
            }
        }
    }
}

#[cfg(test)]
mod test {
    #![allow(non_snake_case)]

    use crate::{
        literal::{Literal, Polarity},
        manager::model::Model,
        vtree::test::right_child,
    };
    use pretty_assertions::assert_eq;
    use std::fs::File;
    use std::io::BufWriter;

    use super::{Sdd, SddManager, SddOptions};

    #[allow(unused)]
    fn quick_draw(manager: &SddManager, sdd: &Sdd, path: &str) {
        let f = File::create(format!("{path}.dot")).unwrap();
        let mut b = BufWriter::new(f);
        manager
            .draw_sdd(&mut b as &mut dyn std::io::Write, sdd)
            .unwrap();

        let f = File::create(format!("{path}_vtree.dot")).unwrap();
        let mut b = BufWriter::new(f);
        manager
            .draw_vtree_graph(&mut b as &mut dyn std::io::Write)
            .unwrap();
    }

    #[allow(unused)]
    fn quick_draw_all(manager: &SddManager, path: &str) {
        let f = File::create(path).unwrap();
        let mut b = BufWriter::new(f);
        manager
            .draw_all_sdds(&mut b as &mut dyn std::io::Write)
            .unwrap();
    }

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
            .rotate_left(&right_child(&root));

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        assert_eq!(a_and_d.vtree_idx, 3);

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d__and_b = manager.conjoin(&a_and_d, &lit_b);
        assert_eq!(a_and_d__and_b.vtree_idx, 3);
    }

    #[test]
    fn model_counting() {
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let root = manager.vtree_manager.borrow().root.clone().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&right_child(&root));

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
                0
            )])]
        );

        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);
        let lit_d = manager.literal("d", Polarity::Positive);

        let root = manager.vtree_manager.borrow().root.clone().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&right_child(&root));

        let a_and_b = manager.conjoin(&lit_a, &lit_b);
        let models = vec![
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", 0),
                Literal::new(Polarity::Positive, "b", 1),
                Literal::new(Polarity::Negative, "c", 2),
                Literal::new(Polarity::Negative, "d", 3),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", 0),
                Literal::new(Polarity::Positive, "b", 1),
                Literal::new(Polarity::Positive, "c", 2),
                Literal::new(Polarity::Negative, "d", 3),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", 0),
                Literal::new(Polarity::Positive, "b", 1),
                Literal::new(Polarity::Negative, "c", 2),
                Literal::new(Polarity::Positive, "d", 3),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", 0),
                Literal::new(Polarity::Positive, "b", 1),
                Literal::new(Polarity::Positive, "c", 2),
                Literal::new(Polarity::Positive, "d", 3),
            ]),
        ];

        assert_eq!(manager.model_enumeration(&a_and_b).all_models(), models);

        let a_and_b_and_c = manager.conjoin(&a_and_b, &lit_c);
        let models = vec![
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", 0),
                Literal::new(Polarity::Positive, "b", 1),
                Literal::new(Polarity::Positive, "c", 2),
                Literal::new(Polarity::Negative, "d", 3),
            ]),
            Model::new_from_literals(vec![
                Literal::new(Polarity::Positive, "a", 0),
                Literal::new(Polarity::Positive, "b", 1),
                Literal::new(Polarity::Positive, "c", 2),
                Literal::new(Polarity::Positive, "d", 3),
            ]),
        ];

        assert_eq!(
            manager.model_enumeration(&a_and_b_and_c).all_models(),
            models
        );

        let a_and_b_and_c_and_d = manager.conjoin(&a_and_b_and_c, &lit_d);
        let models = vec![Model::new_from_literals(vec![
            Literal::new(Polarity::Positive, "a", 0),
            Literal::new(Polarity::Positive, "b", 1),
            Literal::new(Polarity::Positive, "c", 2),
            Literal::new(Polarity::Positive, "d", 3),
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
