use std::collections::HashSet;
use std::hash::Hash;

use crate::literal::Literal;
use crate::SddManager;

type NodeIndex = u64;

#[derive(PartialEq, Eq, Clone)]
// TODO: Implement custom hashing scheme.
pub struct Node {
    sdd: Sdd,

    // Index of the parent node in the SDDManager.nodes vector.
    parent: Option<NodeIndex>,
    index: NodeIndex,
}

impl Node {
    #[must_use]
    pub fn new(sdd: Sdd, parent: Option<NodeIndex>, index: NodeIndex) -> Node {
        Node { sdd, parent, index }
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
// TODO: Implement custom hashing scheme.
pub enum Sdd {
    False,
    True,

    Literal(Literal),

    Decision(SddOr),      // Decision node represents decomposition
    DecisionCompl(SddOr), // Complemented node

    Element(SddAnd),
    ElementCompl(SddAnd),
}

impl Sdd {
    fn is_true(&self) -> bool {
        matches!(self, Sdd::True)
    }

    fn is_false(&self) -> bool {
        matches!(self, Sdd::False)
    }

    fn is_constant(&self) -> bool {
        self.is_true() || self.is_false()
    }

    fn is_literal(&self) -> bool {
        matches!(self, Sdd::Literal(_))
    }

    fn is_decision_node(&self) -> bool {
        matches!(self, Sdd::Decision(_)) || matches!(self, Sdd::DecisionCompl(_))
    }

    fn is_element_node(&self) -> bool {
        matches!(self, Sdd::Element(_)) || matches!(self, Sdd::ElementCompl(_))
    }

    #[must_use]
    pub fn negate(&self) -> Sdd {
        match self {
            Sdd::True => Sdd::False,
            Sdd::False => Sdd::True,
            Sdd::Literal(literal) => Sdd::Literal(Literal::negate(literal)),
            Sdd::Decision(sdd) => Sdd::DecisionCompl(sdd.to_owned()),
            Sdd::DecisionCompl(sdd) => Sdd::Decision(sdd.to_owned()),
            Sdd::Element(sdd) => Sdd::ElementCompl(sdd.to_owned()),
            Sdd::ElementCompl(sdd) => Sdd::Element(sdd.to_owned()),
        }
    }

    #[must_use]
    pub fn is_trimmed(&self, manager: &SddManager) -> bool {
        match self {
            Sdd::True | Sdd::False | Sdd::Literal(_) => true,
            Sdd::Decision(sdd) | Sdd::DecisionCompl(sdd) => sdd.is_trimmed(manager),
            Sdd::Element(sdd) | Sdd::ElementCompl(sdd) => {
                let (prime, sub) = sdd.get_prime_sub(manager);
                prime.sdd.is_trimmed(manager) && sub.sdd.is_trimmed(manager)
            }
        }
    }

    #[must_use]
    pub fn is_compressed(&self, manager: &SddManager) -> bool {
        match self {
            Sdd::True | Sdd::False | Sdd::Literal(_) => true,
            Sdd::Decision(sdd) | Sdd::DecisionCompl(sdd) => sdd.is_compressed(manager),
            Sdd::Element(sdd) | Sdd::ElementCompl(sdd) => {
                let (prime, sub) = sdd.get_prime_sub(manager);
                prime.sdd.is_compressed(manager) && sub.sdd.is_compressed(manager)
            }
        }
    }
}

// Decision node, disjunction of its elements
#[derive(Hash, PartialEq, Eq, Clone)]
#[allow(clippy::module_name_repetitions)]
pub struct SddOr {
    elements: Vec<NodeIndex>,
}

impl SddOr {
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
    pub fn is_trimmed(&self, manager: &SddManager) -> bool {
        let mut primes: HashSet<Sdd> = HashSet::new();

        if self.elements.len() >= 3 {
            return true;
        }

        for element_idx in &self.elements {
            // Check for element `(True, A)`.
            let element: SddAnd = match manager.get_node(element_idx).unwrap().sdd {
                Sdd::ElementCompl(elem) | Sdd::Element(elem) => elem,
                _ => panic!("Decision node must contain only a boxed element!"),
            };

            let (prime, sub) = element.get_prime_sub(manager);

            // Check for `{(true, A)}`.
            if prime.sdd.is_true() {
                return false;
            }
            // Note: Why don't we have to check for symmetric cases `{(A, True)}` and `{(True, A), (False, !A)}` etc.?

            // Check for elements `(A, True)` and `(!A, False)`. We can continue with the next iteration
            // if the sub is not True or False.
            if !sub.sdd.is_constant() {
                continue;
            }

            // Check whether we have already seen this literal but negated.
            if primes.contains(&prime.sdd) {
                return false;
            }

            primes.insert(prime.sdd.negate());
        }

        // Check that elements are also trimmed.
        self.elements
            .iter()
            .all(|el| manager.get_node(el).unwrap().sdd.is_trimmed(manager))
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
    pub fn is_compressed(&self, manager: &SddManager) -> bool {
        let mut subs: HashSet<Sdd> = HashSet::new();
        for element_idx in &self.elements {
            let element: SddAnd = match manager.get_node(element_idx).unwrap().sdd {
                Sdd::ElementCompl(elem) | Sdd::Element(elem) => elem,
                _ => panic!("Decision node must contain only a boxed element!"),
            };

            let sub = element.get_sub(manager);

            if subs.contains(&sub.sdd) {
                return false;
            }

            subs.insert(sub.sdd);
        }

        // Check that all elements are also compressed.
        self.elements
            .iter()
            .all(|el| manager.get_node(el).unwrap().sdd.is_compressed(manager))
    }

    /// Recursivelly trims and compresses SDD.
    ///
    /// SDD is trimmed by traversing bottom up, replacing decompositions {(True, alpha)} and {(alpha, True), (!alpha, False)} with alpha.
    pub fn trim_and_compress(&mut self) {
        todo!("Implement me!")
    }
}

// Element node (a paired box) is a conjunction of prime and sub.
#[allow(clippy::module_name_repetitions)]
#[derive(Hash, PartialEq, Eq, Copy, Clone)]
pub struct SddAnd {
    prime: NodeIndex,
    sub: NodeIndex,
}

impl SddAnd {
    #[must_use]
    pub fn get_prime_sub(&self, manager: &SddManager) -> (Node, Node) {
        (self.get_prime(manager), self.get_sub(manager))
    }

    /// # Panics
    /// Panics if the prime is not in the SDD Manager, which should not happen
    /// under any circumstances.
    #[must_use]
    pub fn get_prime(&self, manager: &SddManager) -> Node {
        manager.get_node(&self.prime).unwrap().clone()
    }

    /// # Panics
    /// Panics if the sub is not in the SDD Manager, which should not happen
    /// under any circumstances.
    #[must_use]
    pub fn get_sub(&self, manager: &SddManager) -> Node {
        manager.get_node(&self.sub).unwrap().clone()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        literal::{Literal, VarLabel},
        options::SddOptions,
        sdd::{Node, Sdd, SddAnd, SddManager, SddOr},
    };

    #[test]
    fn not_trimmed_simple() {
        // TODO: Remove the hardcoded indices once the hashing scheme is implemented.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(2), 0)),
                // Constant `false`.
                (1_u64, Node::new(Sdd::False, Some(2), 1)),
                // Element `(true, false).`
                (
                    2_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 1 }), Some(42), 2),
                ),
                // Decomposition `{(true, false)}`.
                (
                    3_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![2] }), None, 3),
                ),
            ]),
        );

        // Decomposition {(True, False)} is not trimmed.
        let node = manager.get_node(&3_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_simple_2() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Literal `A`.
                (
                    1_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        1,
                    ),
                ),
                // Element `(true, A)`.
                (
                    2_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 1 }), Some(42), 2),
                ),
                // Decomposition `{(true, A)}`.
                (
                    3_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![2] }), None, 3),
                ),
            ]),
        );

        // Decomposition {(A, true)} is not trimmed.
        let node = manager.get_node(&3_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_complex() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(4), 0)),
                // Constant `false`.
                (1_u64, Node::new(Sdd::False, Some(5), 1)),
                // Literal `A`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(4),
                        2,
                    ),
                ),
                // Literal `!A`.
                (
                    3_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(0))),
                        Some(5),
                        3,
                    ),
                ),
                // Element `(A, True)`.
                (
                    4_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 2, sub: 0 }), Some(42), 4),
                ),
                // Element `(!A, False)`.
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 3, sub: 1 }), Some(42), 5),
                ),
                // Decomposition `{(A, true), (!A, false)}`.
                (
                    6_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![4, 5],
                        }),
                        Some(42),
                        6,
                    ),
                ),
            ]),
        );

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager.get_node(&6_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Literal `A`.
                (
                    1_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        1,
                    ),
                ),
                // Literal `!B`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(1))),
                        Some(42),
                        2,
                    ),
                ),
                (
                    3_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 2 }), Some(42), 3),
                ),
                // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
                (
                    4_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![3] }), Some(42), 4),
                ),
                // Element `(A, true)`.
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 1, sub: 0 }), Some(42), 5),
                ),
                // Constant `false`.
                (6_u64, Node::new(Sdd::False, Some(42), 6)),
                // Element `(ptr, false)` where ptr is the decomposition `{(true, !B)}`.
                (
                    7_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 4, sub: 6 }), Some(42), 7),
                ),
                // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
                (
                    8_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![4, 7],
                        }),
                        Some(42),
                        8,
                    ),
                ),
            ]),
        );

        let node = manager.get_node(&7_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_simple() {
        // TODO: Remove the hardcoded indices once the hashing scheme is implemented.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                (0_u64, Node::new(Sdd::False, Some(42), 0)),
                (
                    1_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 0 }), None, 1),
                ),
            ]),
        );

        // Decomposition {(false, false)} is trimmed.
        let node = manager.get_node(&1_u64).unwrap();
        assert!(node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_complex() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `True`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Literal `A`.
                (
                    1_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        1,
                    ),
                ),
                // Literal `!B`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(1))),
                        Some(42),
                        2,
                    ),
                ),
                // Element `(A, true)`.
                (
                    3_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 1, sub: 0 }), Some(42), 3),
                ),
                // Constant `false`.
                (4_u64, Node::new(Sdd::False, Some(42), 4)),
                // Element `(!B, false)`.
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 2, sub: 4 }), Some(42), 5),
                ),
                // Decomposition `{(A, true), (B, false)}`.
                (
                    6_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![3, 5],
                        }),
                        None,
                        6,
                    ),
                ),
            ]),
        );

        // Decomposition {(A, true), (B, false)} is trimmed.
        let node = manager.get_node(&6_u64).unwrap();
        assert!(node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Constant `false`.
                (1_u64, Node::new(Sdd::False, Some(42), 1)),
                // Literal `A`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        2,
                    ),
                ),
                // Literal `!B`.
                (
                    3_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(1))),
                        Some(42),
                        3,
                    ),
                ),
                // Element `(!B, true)`
                (
                    4_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 3, sub: 0 }), Some(42), 4),
                ),
                // Element `(A, true)`
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 2, sub: 0 }), Some(42), 5),
                ),
                // Decomposition `{(!B, true)}`.
                (
                    6_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![4] }), Some(42), 6),
                ),
                // Element `(ptr, false)` where ptr is `{(!B, true)}`.
                (
                    7_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 6, sub: 1 }), Some(42), 7),
                ),
                // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
                (
                    8_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![5, 7],
                        }),
                        Some(42),
                        8,
                    ),
                ),
            ]),
        );

        let node = manager.get_node(&8_u64).unwrap();
        assert!(node.sdd.is_trimmed(&manager));
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
