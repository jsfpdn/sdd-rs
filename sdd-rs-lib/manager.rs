use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter},
    literal::{self, Polarity},
    options::SddOptions,
    sdd::{Decision, Element, Sdd, SddType},
    vtree::{VTree, VTreeManager},
    Result,
};

use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
};

pub(crate) type SddId = usize;

#[derive(Clone, Eq, PartialEq, Hash, Debug, Copy)]
enum Operation {
    Conjoin,
    Disjoin,
}

#[derive(Eq, PartialEq, Hash)]
struct Entry {
    fst: SddId,
    snd: SddId,
    op: Operation,
}

#[allow(clippy::module_name_repetitions)]
pub struct SddManager {
    options: SddOptions,

    vtree_manager: RefCell<VTreeManager>,

    // Unique table holding all the decision nodes.
    // More details can be found in [Algorithms and Data Structures in VLSI Design](https://link.springer.com/book/10.1007/978-3-642-58940-9).
    unique_table: RefCell<HashMap<SddId, Sdd>>,

    // Caches all the computations.
    op_cache: RefCell<HashMap<Entry, SddId>>,
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

    /// # Panics
    /// Function panics if there is no such node with the corresponding id in the unique table.
    #[must_use]
    pub(crate) fn get_node(&self, id: SddId) -> Option<Sdd> {
        self.unique_table.borrow().get(&id).map(|n| n.clone())
    }

    pub fn literal(&self, literal: &str, polarity: Polarity) -> Sdd {
        self.vtree_manager
            .borrow_mut()
            .add_variable(literal::VarLabel::new(literal));

        let literal = Sdd {
            // TODO: Fix vtree index.
            vtree_idx: 0,
            sdd_type: SddType::Literal(literal::Literal::new(polarity, literal)),
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

        if fst.eq_negated(snd) {
            return self.tautology();
        }

        self.apply(fst, snd, Operation::Disjoin)
    }

    #[must_use]
    pub fn negate(&self, fst: &Sdd) -> Sdd {
        Sdd {
            vtree_idx: fst.vtree_idx,
            sdd_type: match fst.sdd_type.clone() {
                SddType::True => SddType::False,
                SddType::False => SddType::True,
                SddType::Literal(literal) => SddType::Literal(literal.negate()),
                SddType::DecisionRegular(decision) => {
                    SddType::DecisionComplement(decision.to_owned())
                }
                SddType::DecisionComplement(decision) => {
                    SddType::DecisionRegular(decision.to_owned())
                }
            },
        }
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
        self.apply(&fst.negate(), snd, Operation::Disjoin)
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
        let fst_con = &self.conjoin(&fst.negate(), &snd.negate());
        let snd_con = &self.conjoin(fst, snd);
        self.disjoin(fst_con, snd_con)
    }

    /// Apply operation on the two Sdds.
    #[must_use]
    fn apply(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> Sdd {
        // TODO: Check post-conditions, namely trimming & compression of the resulting Sdd.
        if fst.is_constant_or_literal() && snd.is_constant_or_literal() {
            return Sdd {
                // TODO: Fix vtree_idx
                vtree_idx: 123,
                sdd_type: match op {
                    // TODO: Fix variable ordering.
                    Operation::Conjoin => SddType::DecisionRegular(Decision {
                        elements: btreeset!(Element {
                            prime: fst.id(),
                            sub: snd.id()
                        }),
                    }),

                    // TODO: Fix variable ordering.
                    Operation::Disjoin => SddType::DecisionRegular(Decision {
                        elements: btreeset!(
                            Element {
                                prime: fst.id(),
                                sub: self.tautology().id(),
                            },
                            Element {
                                prime: snd.id(),
                                sub: self.tautology().id(),
                            }
                        ),
                    }),
                },
            };
        }

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

        self._apply(fst, snd, op)
    }

    fn _apply(&self, fst: &Sdd, snd: &Sdd, op: Operation) -> Sdd {
        let mut gamma = BTreeSet::new();
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

                if res_prime.is_consistent() {
                    let fst_sub = &self.get_node(fst_elem.sub).expect("fst_sub not present");
                    let snd_sub = &self.get_node(snd_elem.sub).expect("snd_sub not present");
                    let res_sub = match op {
                        Operation::Conjoin => self.disjoin(fst_sub, snd_sub),
                        Operation::Disjoin => self.conjoin(fst_sub, snd_sub),
                    };

                    // TODO: Should we cache primes and subs computed here? The paper caches only the resulting SDD.
                    self.insert_node(&res_prime);
                    self.insert_node(&res_sub);
                    gamma.insert(Element {
                        prime: res_prime.id(),
                        sub: res_sub.id(),
                    });
                    dbg!(("inserted nodes", res_prime, res_sub));
                }
            }
        }

        let result = Sdd::unique_d(gamma);
        self.insert_node(&result);
        self.cache_operation(fst.id(), snd.id(), op, result.id());
        println!("{:?} {:?} {:?} = {:?}", fst, op, snd, result);

        result
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

    fn insert_node(&self, sdd: &Sdd) {
        self.unique_table.borrow_mut().insert(sdd.id(), sdd.clone());
    }

    fn cache_operation(&self, fst: SddId, snd: SddId, op: Operation, res_id: SddId) {
        self.op_cache
            .borrow_mut()
            .insert(Entry { fst, snd, op }, res_id);
    }
}

#[cfg(test)]
mod test {
    use crate::{
        btreeset,
        literal::Polarity,
        sdd::{Decision, Element, Sdd, SddType},
    };

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

        let a_and_b = manager.conjoin(&lit_a, &lit_b);
        assert_eq!(
            Sdd {
                // TODO: Fix vtree_idx
                vtree_idx: 123,
                sdd_type: SddType::DecisionRegular(Decision {
                    elements: btreeset!(Element {
                        prime: lit_a.id(),
                        sub: lit_b.id()
                    })
                }),
            },
            a_and_b
        );

        let a_or_b = manager.disjoin(&lit_a, &lit_b);
        assert_eq!(
            Sdd {
                // TODO: Fix vtree_idx
                vtree_idx: 123,
                sdd_type: SddType::DecisionRegular(Decision {
                    elements: btreeset!(
                        Element {
                            prime: lit_a.id(),
                            sub: manager.tautology().id()
                        },
                        Element {
                            prime: lit_b.id(),
                            sub: manager.tautology().id()
                        }
                    )
                }),
            },
            a_or_b
        );

        // TODO: Implement is_consistent next to unlock more complicated apply scenarios.
    }
}
