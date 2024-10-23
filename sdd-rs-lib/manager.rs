use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter},
    literal::{self, Polarity},
    options::SddOptions,
    sdd::{Element, Sdd, SddType},
    vtree::{VTreeManager, VTreeOrder},
    Result,
};

use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
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
            op_cache: RefCell::new(HashMap::new()),
            unique_table,
        }
    }

    // TODO: This function should be removed as user should not be able to fill the unique_table
    // directly.
    #[must_use]
    pub(crate) fn new_with_nodes(options: SddOptions, sdds: &[Sdd]) -> SddManager {
        let mut table = HashMap::new();
        for sdd in sdds {
            table.insert(sdd.id(), sdd.clone());
        }
        table.insert(Sdd::new_true().id(), Sdd::new_true());
        table.insert(Sdd::new_false().id(), Sdd::new_false());

        SddManager {
            options,
            vtree_manager: RefCell::new(VTreeManager::new()),
            unique_table: RefCell::new(table),
            op_cache: RefCell::new(HashMap::new()),
        }
    }

    pub(crate) fn dump_nodes(&self) {
        for (id, node) in self.unique_table.borrow().iter() {
            println!("({id}) {node:?}");
        }
    }

    /// # Panics
    /// Function panics if there is no such node with the corresponding id in the unique table.
    #[must_use]
    pub(crate) fn get_node(&self, id: usize) -> Option<Sdd> {
        self.unique_table.borrow().get(&id).map(|n| n.clone())
    }

    pub fn literal(&self, literal: &str, polarity: Polarity) -> Sdd {
        let var_label = literal::VarLabel::new(literal);
        self.vtree_manager.borrow_mut().add_variable(&var_label);
        let vtree_idx = self
            .vtree_manager
            .borrow()
            .get_variable_vtree(&var_label)
            .expect("var_label was just inserted, therefore it must be present and found")
            .borrow()
            .get_index();

        let literal = Sdd {
            sdd_type: SddType::Literal(literal::Literal::new(polarity, literal)),
            negation: None,
            vtree_idx,
        };

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

        if fst.eq_negated(snd) {
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

        if fst.eq_negated(snd) {
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

        if fst.eq_negated(snd) {
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

        if fst.eq_negated(snd) {
            return self.contradiction();
        }

        // Relies on the fact that A <=> B is equivalent (!A && !B) || (A && B).
        let fst_con = &self.conjoin(&fst.clone().negate(self), &snd.clone().negate(self));
        let snd_con = &self.conjoin(fst, snd);
        self.disjoin(fst_con, snd_con)
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

        debug_assert!(sdd.is_trimmed(self));
        debug_assert!(sdd.is_compressed(self));

        sdd
    }

    fn _apply_eq(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> BTreeSet<Element> {
        let mut elements = BTreeSet::new();
        for fst_elem in fst.expand().elements.iter() {
            for snd_elem in snd.expand().elements.iter() {
                let res_prime = self.conjoin(
                    &self
                        .get_node(fst_elem.prime)
                        .expect("fst_prime not present"),
                    &self
                        .get_node(snd_elem.prime)
                        .expect("snd_prime not present"),
                );

                if res_prime.is_false() {
                    let fst_sub = &self.get_node(fst_elem.sub).expect("fst_sub not present");
                    let snd_sub = &self.get_node(snd_elem.sub).expect("snd_sub not present");
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
        unimplemented!("_apply_left_sub_of_right not yet implemented")
    }

    fn _apply_right_sub_of_left(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> BTreeSet<Element> {
        assert!(fst.vtree_idx < snd.vtree_idx);
        unimplemented!("_apply_right_sub_of_left not yet implemented")
    }

    pub fn condition() {}
    pub fn exist() {}
    pub fn forall() {}

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_sdd_graph<'b>(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        let mut dot_writer = DotWriter::new(String::from("sdd"));
        for node in self.unique_table.borrow().values() {
            node.draw(&mut dot_writer, self);
        }
        dot_writer.write(writer)
    }

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_vtree_graph<'b>(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        let mut dot_writer = DotWriter::new(String::from("vtree"));
        self.vtree_manager.borrow().draw(&mut dot_writer, self);
        dot_writer.write(writer)
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
}

#[cfg(test)]
mod test {
    use crate::{literal::Polarity, vtree::test::right_child};

    use super::{SddManager, SddOptions};

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
    fn literal_apply() {
        let manager = SddManager::new(SddOptions::default());

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);

        // let a_and_b = manager.conjoin(&lit_a, &lit_b);
        // TODO: Fix these tests.
    }

    #[test]
    fn apply() {
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
        let root = manager.vtree_manager.borrow().root.clone().unwrap();
        manager
            .vtree_manager
            .borrow_mut()
            .rotate_left(&right_child(&root));

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        let a_and_d = manager.conjoin(&lit_a, &lit_d);
        assert_eq!(a_and_d.vtree_idx, 3);

        // Resulting SDD must be normalized w.r.t. vtree with index 3.
        // let a_and_d__and_b = manager.conjoin(&a_and_d, &lit_b);
        // assert_eq!(a_and_d__and_b.vtree_idx, 2);

        // let f = std::fs::File::create("test-out-sdd.dot").unwrap();
        // let mut b = std::io::BufWriter::new(f);
        // manager
        //     .draw_sdd_graph(&mut b as &mut dyn std::io::Write)
        //     .unwrap();

        // manager.dump_nodes();
    }
}
