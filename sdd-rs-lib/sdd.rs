use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;

use crate::btreeset;
use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::Literal,
    manager::{SddId, SddManager},
};

#[derive(PartialEq, Eq, Clone, Hash)]
pub(crate) struct Node {
    decision: Decision,

    parents: u64,
    refs: u64,
    // TODO: Do we want field `parents: BTreeSet<u64>`? What would this point to? Since only the
    // decision nodes will be stored in the unique_table, then it would have to point to decision
    // node, not to the particular element pointing to it (since it is not hashed and stored
    // directly in the unique_table).
}

impl Node {
    #[must_use]
    pub fn new(decision: Decision) -> Node {
        Node {
            decision,
            parents: 0,
            refs: 0,
        }
    }
}

// Element node (a paired box) is a conjunction of prime and sub.
#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug, Copy)]
pub(crate) struct Element {
    pub(crate) prime: SddId,
    pub(crate) sub: SddId,
}

impl Element {
    fn is_trimmed(&self, manager: &SddManager) -> bool {
        let (prime, sub) = self.get_prime_sub(manager);
        prime.is_trimmed(manager) && sub.is_trimmed(manager)
    }

    fn is_compressed(&self, manager: &SddManager) -> bool {
        let (prime, sub) = self.get_prime_sub(manager);
        prime.is_compressed(manager) && sub.is_compressed(manager)
    }

    fn get_prime_sub<'a>(&self, manager: &'a SddManager) -> (Sdd, Sdd) {
        (
            manager
                .get_node(self.prime)
                .expect("element_prime not present in unique_table"),
            manager
                .get_node(self.sub)
                .expect("element_sub not present in unique_table"),
        )
    }
}

impl Dot for Element {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager) {
        let idx = fxhash::hash(self);

        let (prime, sub) = self.get_prime_sub(manager);

        writer.add_node(idx, NodeType::Record(prime.dot_repr(), sub.dot_repr()));

        if let Sdd {
            sdd_type: SddType::DecisionRegular(node) | SddType::DecisionComplement(node),
            ..
        } = manager
            .get_node(self.prime)
            .expect("element_prime not present in unique_table")
        {
            writer.add_edge(Edge::Prime(idx, fxhash::hash(&node)));
        }
        if let Sdd {
            sdd_type: SddType::DecisionRegular(node) | SddType::DecisionComplement(node),
            ..
        } = manager
            .get_node(self.sub)
            .expect("element_sub not present in unique_table")
        {
            writer.add_edge(Edge::Sub(idx, fxhash::hash(&node)));
        };
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub enum SddType {
    True,
    False,
    Literal(Literal),
    DecisionRegular(Decision),
    DecisionComplement(Decision),
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct Sdd {
    pub(crate) sdd_type: SddType,
    pub(crate) vtree_idx: u16,
}

impl Dot for Sdd {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager) {
        let mut idx = fxhash::hash(self);
        let node_type = match self.sdd_type.clone() {
            SddType::True => NodeType::Box("True".to_string()),
            SddType::False => NodeType::Box("False".to_string()),
            SddType::Literal(literal) => NodeType::Box(format!("{literal}")),
            SddType::DecisionComplement(node) | SddType::DecisionRegular(node) => {
                idx = fxhash::hash(&node);
                for elem in node.elements.iter() {
                    elem.draw(writer, manager);
                    writer.add_edge(Edge::Simple(idx, fxhash::hash(&elem)));
                }
                // TODO: Add proper vtree index to the NodeType::Circle once implemented.
                NodeType::Circle(42)
            }
        };

        writer.add_node(idx, node_type);
    }
}

impl Sdd {
    #[must_use]
    pub fn new_true() -> Sdd {
        Sdd {
            sdd_type: SddType::True,
            vtree_idx: 0,
        }
    }

    #[must_use]
    pub fn new_false() -> Sdd {
        Sdd {
            sdd_type: SddType::False,
            vtree_idx: 0,
        }
    }

    #[must_use]
    pub fn id(&self) -> usize {
        match self.sdd_type.clone() {
            SddType::DecisionComplement(decision) | SddType::DecisionRegular(decision) => {
                fxhash::hash(&decision)
            }
            _ => fxhash::hash(self),
        }
    }

    pub fn is_true(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::True,
                ..
            }
        )
    }

    pub fn is_false(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::False,
                ..
            }
        )
    }

    pub fn is_constant(&self) -> bool {
        self.is_true() || self.is_false()
    }

    pub fn is_literal(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::Literal(_literal),
                ..
            }
        )
    }

    pub fn is_constant_or_literal(&self) -> bool {
        self.is_constant() || self.is_literal()
    }

    pub fn is_decision_regular(&self) -> bool {
        match self.sdd_type {
            SddType::DecisionRegular(_) => true,
            SddType::DecisionComplement(_) => false,
            _ => panic!("only decision nodes can be regular or complemented!"),
        }
    }

    pub(crate) fn expand(&self) -> Decision {
        match self.sdd_type {
            SddType::True => Decision {
                elements: btreeset!(Element {
                    prime: Sdd::new_true().id(),
                    sub: Sdd::new_true().id()
                }),
            },
            SddType::False => Decision {
                elements: btreeset!(Element {
                    prime: Sdd::new_true().id(),
                    sub: Sdd::new_false().id()
                }),
            },
            // TODO: Is this conceptually correct?
            SddType::Literal(_) => Decision {
                elements: btreeset!(Element {
                    prime: self.id(),
                    sub: Sdd::new_false().id()
                }),
            },
            // TODO: What about complented decision nodes?
            SddType::DecisionRegular(ref dec) | SddType::DecisionComplement(ref dec) => dec.clone(),
        }
    }

    pub(crate) fn negate(&self) -> Sdd {
        // TODO: Negation preserves vtree_index?
        Sdd {
            sdd_type: match self.sdd_type.clone() {
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
            vtree_idx: self.vtree_idx,
        }
    }

    pub fn eq_negated(&self, other: &Sdd) -> bool {
        match (self.sdd_type.clone(), other.sdd_type.clone()) {
            (SddType::True, SddType::False) | (SddType::False, SddType::True) => true,
            (SddType::Literal(fst), SddType::Literal(snd)) => fst.eq_negated(&snd),
            // TODO: Is this correct? This smells fishy.
            (SddType::DecisionRegular(fst), SddType::DecisionComplement(snd))
            | (SddType::DecisionComplement(fst), SddType::DecisionRegular(snd)) => fst == snd,
            (_, _) => false,
        }
    }

    fn is_trimmed(&self, manager: &SddManager) -> bool {
        match self.sdd_type.clone() {
            SddType::True | SddType::False | SddType::Literal(_) => true,
            SddType::DecisionRegular(decision) | SddType::DecisionComplement(decision) => {
                decision.is_trimmed(manager)
            }
        }
    }

    fn is_compressed(&self, manager: &SddManager) -> bool {
        match self.sdd_type.clone() {
            SddType::True | SddType::False | SddType::Literal(_) => true,
            SddType::DecisionRegular(decision) | SddType::DecisionComplement(decision) => {
                decision.is_compressed(manager)
            }
        }
    }

    pub fn is_consistent(&self) -> bool {
        unimplemented!();
    }

    pub(crate) fn unique_d<'b>(gamma: BTreeSet<Element>) -> Sdd {
        // gamma == {(T, T)}?
        if gamma.eq(&btreeset!(Element {
            prime: Sdd::new_true().id(),
            sub: Sdd::new_true().id()
        })) {
            return Sdd::new_true();
        }

        // gamma == {(T, F)}?
        if gamma.eq(&btreeset!(Element {
            prime: Sdd::new_true().id(),
            sub: Sdd::new_false().id()
        })) {
            return Sdd::new_false();
        }

        Sdd {
            sdd_type: SddType::DecisionRegular(Decision { elements: gamma }),
            // TODO: What's the proper vtree index?
            vtree_idx: 0,
        }
    }

    fn dot_repr(&self) -> String {
        match self.sdd_type.clone() {
            SddType::True => String::from("⊤"),
            SddType::False => String::from("⊥"),
            SddType::Literal(literal) => format!("{literal}"),
            _ => String::new(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct Decision {
    pub(crate) elements: BTreeSet<Element>,
}

impl Decision {
    /// Recursivelly checks whether the decision node is trimmed.
    /// Decision node is `trimmed` if it does not contain decompositions of the form `{(True, A)}` or
    /// `{(A, True), (!A, False)}`.
    ///
    /// See definition 8 in [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    ///
    /// # Panics
    /// Function panics if
    /// * elements are not stored in the SDD manager,
    /// * the decision node contains something else than boxed elements.
    #[must_use]
    pub(crate) fn is_trimmed(&self, manager: &SddManager) -> bool {
        let mut primes: HashSet<Sdd> = HashSet::new();

        if self.elements.len() >= 3 {
            return true;
        }

        for element in &self.elements {
            let (prime, sub) = element.get_prime_sub(manager);

            // Check for `{(true, A)}`.
            if prime.is_true() {
                return false;
            }

            // Check for elements `(A, True)` and `(!A, False)`. We can continue with the next iteration
            // if the sub is not True or False.
            if !sub.is_constant() {
                continue;
            }

            // Check whether we have already seen this literal but negated.
            if primes.contains(&prime) {
                return false;
            }

            primes.insert(prime.negate());
        }

        // Check that elements are also trimmed.
        self.elements.iter().all(|el| el.is_trimmed(manager))
    }

    /// Recursivelly checks whether the decision node is compressed.
    /// Decision node is compressed if all subs are distinct, i.e., for all indexes i,j such that i != j,
    /// it holds that `s_i != s_j`.
    ///
    /// See definition 8 in [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    ///
    /// # Panics
    /// Function panics if
    /// * elements are not stored in the SDD manager,
    /// * the decision node contains something else than boxed elements.
    #[must_use]
    pub(crate) fn is_compressed(&self, manager: &SddManager) -> bool {
        let mut subs: HashSet<Sdd> = HashSet::new();
        for element in &self.elements {
            let (_, sub) = element.get_prime_sub(manager);
            if subs.contains(&sub) {
                return false;
            }

            subs.insert(sub);
        }

        // Check that all elements are also compressed.
        self.elements.iter().all(|el| el.is_compressed(manager))
    }

    /// Recursivelly trims and compresses SDD.
    ///
    /// SDD is trimmed by traversing bottom up, replacing decompositions {(true, alpha)} and {(alpha, true), (!alpha, false)} with alpha.
    /// SDD is decompressed by repeatedly replacing elements `(p, s)` and `(q, s)` with
    /// `(p || q, s)`.
    pub(crate) fn trim_and_compress(&mut self) {
        unimplemented!()
    }
}

#[cfg(test)]
mod test {
    use super::{Element, Sdd, SddType};
    use crate::literal::{Literal, Polarity};

    #[test]
    fn not_trimmed_simple() {
        // TODO: Fix tests to use the hashes. This means properly loading the table with nodes.
        // let element = Element {
        //     prime: Sdd::True,
        //     sub: Sdd::False,
        // };

        // // Decomposition `{(true, false)}`.
        // let decision = &Decision {
        //     elements: btreeset!(&element),
        // };
        // let sdd = &Sdd::DecisionRegular(decision);

        // let decisions = &vec![sdd];
        // let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // // Decomposition {(True, False)} is not trimmed.
        // let node = manager.get_node(sdd.id());
        // assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_simple_2() {
        // let element = Element {
        //     prime: &Sdd::True,
        //     sub: &boxed_literal(Polarity::Positive, "A"),
        // };

        // // Decomposition `{(true, A)}`.
        // let decision = &Decision {
        //     elements: btreeset!(&element),
        // };
        // let sdd = &Sdd::DecisionRegular(decision);

        // let decisions = &vec![sdd];
        // let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // // Decomposition {(A, true)} is not trimmed.
        // let node = manager.get_node(sdd.id());
        // assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_complex() {
        // let element_1 = Element {
        //     prime: &boxed_literal(Polarity::Positive, "A"),
        //     sub: &Sdd::True,
        // };
        // let element_2 = Element {
        //     prime: &boxed_literal(Polarity::Negative, "A"),
        //     sub: &Sdd::False,
        // };

        // // Decomposition `{(A, true), (!A, false)}`.
        // let decision = &Decision {
        //     elements: btreeset!(&element_1, &element_2),
        // };
        // let sdd = &Sdd::DecisionRegular(decision);

        // let decisions = &vec![sdd];
        // let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        // let node = manager.get_node(sdd.id());
        // assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_recursive() {
        // // Check that decomposition is recursivelly checked.
        // let element_1_1 = Element {
        //     prime: &Sdd::True,
        //     sub: &boxed_literal(Polarity::Negative, "B"),
        // };

        // // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
        // let decision_1 = &Decision {
        //     elements: btreeset!(&element_1_1),
        // };

        // let sdd_1 = &Sdd::DecisionRegular(decision_1);

        // let element_2_1 = Element {
        //     prime: &boxed_literal(Polarity::Positive, "A"),
        //     sub: &Sdd::True,
        // };

        // let element_2_2 = Element {
        //     prime: &Sdd::DecisionRegular(decision_1),
        //     sub: &Sdd::False,
        // };

        // // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
        // let decision_2 = &Decision {
        //     elements: btreeset!(&element_2_1, &element_2_2),
        // };

        // let sdd_2 = &Sdd::DecisionRegular(decision_2);

        // let decisions = &vec![sdd_1, sdd_2];
        // let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_complex() {
        // let element_1 = Element {
        //     prime: &boxed_literal(Polarity::Positive, "A"),
        //     sub: &Sdd::True,
        // };
        // let element_2 = Element {
        //     prime: &boxed_literal(Polarity::Positive, "A"),
        //     sub: &Sdd::False,
        // };

        // // Decomposition `{(A, true), (B, false)}`.
        // let decision = &Decision {
        //     elements: btreeset!(&element_1, &element_2),
        // };
        // let sdd = &Sdd::DecisionRegular(decision);

        // let decisions = &vec![sdd];
        // let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // // Decomposition {(A, true), (B, false)} is trimmed.
        // let node = manager.get_node(sdd.id());
        // assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        // let element_1_1 = Element {
        //     prime: &boxed_literal(Polarity::Negative, "B"),
        //     sub: &Sdd::True,
        // };

        // // Decomposition `{(!B, true)}`.
        // let decision_1 = &Decision {
        //     elements: btreeset!(&element_1_1),
        // };
        // let sdd_1 = &Sdd::DecisionRegular(decision_1);

        // let element_2_1 = Element {
        //     prime: &boxed_literal(Polarity::Positive, "A"),
        //     sub: &Sdd::True,
        // };
        // let element_2_2 = Element {
        //     prime: sdd_1,
        //     sub: &Sdd::False,
        // };

        // // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
        // let decision_2 = &Decision {
        //     elements: btreeset!(&element_2_1, &element_2_2),
        // };
        // let sdd_2 = &Sdd::DecisionRegular(decision_2);

        // let decisions = &vec![sdd_1, sdd_2];
        // let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // let node = manager.get_node(sdd_2.id());
        // assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn not_compressed() {
        // TODO: Implement me!
    }

    #[test]
    fn compressed() {
        // TODO: Implement me!
    }
}
