use core::fmt;
use std::{collections::BTreeSet, hash::Hash};

use bitvec::vec::BitVec;

use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::Literal,
    manager::SddManager,
    sdd::{Decision, Element},
    vtree::VTreeRef,
};

/// Given the following vtree rooted at `x`:
/// ```ignore
///        x
///      /   \
///     w     c
///   /   \
///  a     b
/// ```
/// an SDD normalized for `x` must depend on some variable in sub-vtree `c`
/// and also on some variable in sub-vtree `a`, `b`, or both.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum LeftDependence {
    /// SDD normalized for `x` depends only on some variable in sub-vtree `a`, not `b`.
    A,
    /// SDD normalized for `x` depends only on some variable in sub-vtree `b`, not `a`.
    B,
    /// SDD normalized for `x` depends on some variables in both sub-vtrees `a` and `b`.
    AB,
}

/// Given the following vtree rooted at `w`:
/// ```ignore
///      w
///    /   \
///   a     x
///       /   \
///      b     c
/// ```
/// an SDD normalized for `w` must depend on some variable in sub-vtree `a`
/// and also on some variable in sub-vtree `b`, `c`, or both.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum RightDependence {
    /// SDD normalized for `x` depends only on some variable in sub-vtree `b`, not `c`.
    B,
    /// SDD normalized for `x` depends only on some variable in sub-vtree `c`, not `b`.
    C,
    /// SDD normalized for `x` depends on some variables in both sub-vtrees `b` and `c`.
    BC,
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub(crate) enum SddType {
    True,
    False,
    Literal(Literal),
    Decision(Decision),
}

impl SddType {
    #[must_use]
    pub fn id(&self) -> usize {
        fxhash::hash(self)
    }

    pub(crate) fn name(&self) -> &str {
        match self {
            SddType::False => "false",
            SddType::True => "true",
            SddType::Literal(..) => "literal",
            SddType::Decision(..) => "decision",
        }
    }

    pub(crate) fn elements(&self) -> Option<BTreeSet<Element>> {
        match self {
            SddType::Decision(Decision { elements }) => Some(elements.clone()),
            _ => None,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub struct Sdd {
    pub(crate) sdd_idx: u16,
    pub(crate) sdd_type: SddType,
    pub(crate) vtree_idx: u16,
    pub(crate) negation: Option<usize>,
    pub(crate) model_count: Option<u64>,
    pub(crate) models: Option<Vec<BitVec>>,
}

impl fmt::Debug for Sdd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sdd")
            .field("sdd_type", &self.sdd_type)
            .field("vtree_idx", &self.vtree_idx)
            .field("id", &self.id())
            .finish()
    }
}

impl Dot for Sdd {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager) {
        match self.sdd_type.clone() {
            // Do not render literals and constants as they do not provide any
            // value and only take up space.
            SddType::True | SddType::False | SddType::Literal(..) => return,
            SddType::Decision(node) => {
                let idx = fxhash::hash(&node);
                for elem in node.elements.iter() {
                    elem.draw(writer, manager);
                    writer.add_edge(Edge::Simple(idx, fxhash::hash(&elem)));
                }
                let node_type = NodeType::Circle(self.vtree_idx, Some(self.id()));
                writer.add_node(idx, node_type);
            }
        };
    }
}

impl Sdd {
    #[must_use]
    pub(crate) fn new(sdd_type: SddType, vtree_idx: u16, negation: Option<usize>) -> Sdd {
        let (model_count, models) = match sdd_type.clone() {
            SddType::False => (Some(0), None),
            SddType::True => (Some(1), None),
            SddType::Literal(literal) => (Some(1), None),
            _ => (None, None),
        };

        Sdd {
            sdd_idx: 0,
            sdd_type,
            vtree_idx,
            negation,
            model_count,
            models,
        }
    }

    #[must_use]
    pub(crate) fn new_true() -> Sdd {
        Self::new(SddType::True, 0, None)
    }

    #[must_use]
    pub(crate) fn new_false() -> Sdd {
        Self::new(SddType::False, 0, None)
    }

    #[must_use]
    pub fn id(&self) -> usize {
        // Do not take vtree index, id of negated sdd and number of models into account.
        self.sdd_type.id()
    }

    /// Check whether the SDD represent a true constant.
    pub fn is_true(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::True,
                ..
            }
        )
    }

    /// Check whether the SDD represent a false constant.
    pub fn is_false(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::False,
                ..
            }
        )
    }

    /// Check whether the SDD represents either the true or false constants.
    pub fn is_constant(&self) -> bool {
        self.is_true() || self.is_false()
    }

    /// Check whether the SDD represents a literal.
    pub fn is_literal(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::Literal(_literal),
                ..
            }
        )
    }

    /// Check whether the SDD represents either a constant or literal.
    pub fn is_constant_or_literal(&self) -> bool {
        self.is_constant() || self.is_literal()
    }

    /// Expand the SDD into a decision node as described in Algorithm 1 in
    /// [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
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
            SddType::Literal(_) => Decision {
                elements: btreeset!(Element {
                    prime: self.id(),
                    sub: Sdd::new_false().id()
                }),
            },
            SddType::Decision(ref dec) => dec.clone(),
        }
    }

    /// Negate the SDD and cache it.
    ///
    /// The computation works lazily - if the negation has been already computed,
    /// the value is just returned.
    pub(crate) fn negate(&mut self, manager: &SddManager) -> Sdd {
        if let Some(negated_sdd_id) = self.negation {
            return manager.get_node(negated_sdd_id).unwrap();
        }

        if let SddType::Decision(dec) = self.sdd_type.clone() {
            let mut elements = BTreeSet::new();
            for Element { prime, sub } in dec.elements {
                let sub = manager.get_node(sub).unwrap().negate(manager);

                elements.insert(Element {
                    prime,
                    sub: sub.id(),
                });
            }

            let negated_sdd = Sdd::new(
                SddType::Decision(Decision { elements }),
                self.vtree_idx,
                Some(self.id()),
            );

            // Add the negation to the unique table and update the original SDD
            // in the unique table to point to this new negation.
            self.negation = Some(negated_sdd.id());
            manager.insert_node(self);
            manager.insert_node(&negated_sdd);

            return negated_sdd;
        }

        let sdd_type = match self.sdd_type.clone() {
            SddType::True => SddType::False,
            SddType::False => SddType::True,
            SddType::Literal(literal) => SddType::Literal(literal.negate()),
            SddType::Decision(..) => {
                panic!("cannot happen - bug in the if expression's condition")
            }
        };

        let negated_sdd = Sdd::new(sdd_type, self.vtree_idx, None);

        // Cache the negation.
        manager.insert_node(&negated_sdd);

        negated_sdd
    }

    /// Check whether [`self`] equals to negated [`other`].
    pub(crate) fn eq_negated(&self, other: &Sdd, manager: &SddManager) -> bool {
        match (self.sdd_type.clone(), other.sdd_type.clone()) {
            (SddType::True, SddType::False) | (SddType::False, SddType::True) => true,
            (SddType::Literal(fst), SddType::Literal(snd)) => fst.eq_negated(&snd),
            (SddType::Decision(..), SddType::Decision(..)) => {
                self.clone().negate(manager).id() == other.id()
            }
            (_, _) => false,
        }
    }

    /// Recursively check whether [`self`] and all its descendants are trimmed.
    /// SDD is trimmed if it does not contain decompositions in the form of
    /// `{(true, alpha)}` and `{(alpha, true), (!alpha, false)}`.
    pub fn is_trimmed(&self, manager: &SddManager) -> bool {
        match self.sdd_type.clone() {
            SddType::True | SddType::False | SddType::Literal(_) => true,
            SddType::Decision(decision) => decision.is_trimmed(manager),
        }
    }

    /// Recursively check whether [`self`] and all its descendants are compressed.
    /// SDD is compressed if no elements share a sub.
    pub fn is_compressed(&self, manager: &SddManager) -> bool {
        match self.sdd_type.clone() {
            SddType::True | SddType::False | SddType::Literal(_) => true,
            SddType::Decision(decision) => decision.is_compressed(manager),
        }
    }

    /// Canonicalize SDD by trimming and compressing it. Only decision nodes can
    /// be canonicalized. Returns the SDD and flag whether it had to be canonicalized or not.
    ///
    /// Decision node is trimmed by replacing decompositions {(true, alpha)}
    /// and {(alpha, true), (!alpha, false)} with alpha. SDD is compressed by repeatedly
    /// replacing elements `(p, s)` and `(q, s)` with `(p || q, s)`.
    #[must_use]
    pub(crate) fn canonicalize(&self, manager: &SddManager) -> Sdd {
        match &self.sdd_type {
            SddType::Decision(decision) => {
                if let Some(trimmed_sdd) = decision.trim(manager) {
                    trimmed_sdd
                } else {
                    let decision = decision.compress(manager);
                    if let Some(trimmed_sdd) = decision.trim(manager) {
                        trimmed_sdd
                    } else {
                        Sdd::new(
                            SddType::Decision(decision.clone()),
                            self.vtree_idx,
                            self.negation, // TODO: Double check this.
                        )
                    }
                }
            }
            _ => self.clone(),
        }
    }

    /// Compute "uniqueD" SDD as described in Algorithm 1 in
    /// [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    pub(crate) fn unique_d<'b>(gamma: BTreeSet<Element>, vtree_idx: u16) -> Sdd {
        // gamma == {(T, T)}?
        if gamma.eq(&btreeset![Element {
            prime: Sdd::new_true().id(),
            sub: Sdd::new_true().id(),
        }]) {
            return Sdd::new_true();
        }

        // gamma == {(T, F)}?
        if gamma.eq(&btreeset![Element {
            prime: Sdd::new_true().id(),
            sub: Sdd::new_false().id(),
        }]) {
            return Sdd::new_false();
        }

        Sdd::new(
            SddType::Decision(Decision { elements: gamma }),
            vtree_idx,
            None,
        )
    }

    pub(super) fn dot_repr(&self) -> String {
        match self.sdd_type.clone() {
            SddType::True => String::from("⊤"),
            SddType::False => String::from("⊥"),
            SddType::Literal(literal) => format!("{literal}"),
            _ => String::new(),
        }
    }

    #[must_use]
    pub(crate) fn dependence_on_left_vtree(
        &self,
        w: &VTreeRef,
        manager: &SddManager,
    ) -> LeftDependence {
        assert_eq!(self.vtree_idx, w.borrow().get_index());

        let SddType::Decision(ref decision) = self.sdd_type else {
            panic!("cannot get dependence on anything other than decision node");
        };

        let primes: Vec<Sdd> = decision.primes(&manager).iter().cloned().collect();
        // No need to filter out constants from collected primes since they cannot
        // occur as primes of elements.

        let mut depends_on_a = false;
        let mut depends_on_b = false;
        let w_idx = w.borrow().get_index();

        for prime in &primes {
            if prime.vtree_idx == w_idx {
                return LeftDependence::AB;
            }

            if prime.vtree_idx < w_idx {
                depends_on_a = true;
            } else {
                depends_on_b = true;
            }

            if depends_on_a && depends_on_b {
                return LeftDependence::AB;
            }
        }

        if depends_on_a {
            return LeftDependence::A;
        }

        LeftDependence::B
    }

    #[must_use]
    pub(crate) fn dependence_on_right_vtree(
        &self,
        x: &VTreeRef,
        manager: &SddManager,
    ) -> RightDependence {
        assert_eq!(self.vtree_idx, x.borrow().get_index());

        let SddType::Decision(ref decision) = self.sdd_type else {
            panic!("cannot get dependence on anything other than decision node");
        };

        let subs: Vec<Sdd> = decision
            .subs(&manager)
            .iter()
            .filter(|sub| !sub.is_constant())
            .cloned()
            .collect();

        let mut depends_on_b = false;
        let mut depends_on_c = false;
        let x_idx = x.borrow().get_index();

        for sub in &subs {
            if sub.vtree_idx == x_idx {
                return RightDependence::BC;
            }

            if sub.vtree_idx < x_idx {
                depends_on_b = true;
            } else {
                depends_on_c = true;
            }

            if depends_on_b && depends_on_c {
                return RightDependence::BC;
            }
        }

        if depends_on_b {
            return RightDependence::B;
        }

        RightDependence::C
    }
}

#[cfg(test)]
mod test {
    use super::{Decision, Element, Sdd, SddType};
    use crate::btreeset;
    use crate::literal::{Literal, Polarity};
    use crate::manager::{options::SddOptions, SddManager};
    use crate::sdd::{LeftDependence, RightDependence};
    use crate::util::{quick_draw, quick_draw_all};

    #[test]
    fn not_trimmed_simple() {
        let element = Element {
            prime: (Sdd::new_true().id()),
            sub: (Sdd::new_false().id()),
        };

        // Decomposition `{(true, false)}`.
        let decision = Decision {
            elements: btreeset!(element),
        };
        let sdd = Sdd::new(SddType::Decision(decision), 0, None);
        let decisions = &vec![sdd.clone()];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition {(True, False)} is not trimmed.
        let node = manager
            .get_node(sdd.id())
            .expect("node is not present in the unique table");
        assert!(!node.is_trimmed(&manager));

        let node = node.canonicalize(&manager);
        assert!(node.is_trimmed(&manager));
        assert_eq!(node, Sdd::new_false());
    }

    fn create_literal(literal: Literal) -> Sdd {
        Sdd::new(SddType::Literal(literal), 0, None)
    }

    #[test]
    fn not_trimmed_simple_2() {
        let mut all_sdds: Vec<Sdd> = vec![];

        let a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let element = Element {
            prime: (Sdd::new_true().id()),
            sub: (a.id()),
        };

        all_sdds.push(a);

        // // Decomposition `{(true, A)}`.
        let decision = Decision {
            elements: btreeset!(element),
        };
        let sdd = Sdd::new(SddType::Decision(decision), 0, None);
        all_sdds.push(sdd.clone());

        let manager = SddManager::new_with_nodes(SddOptions::new(), &all_sdds);

        // Decomposition {(A, true)} is not trimmed.
        let node = manager
            .get_node(sdd.id())
            .expect("node is not present in the unique table");
        assert!(!node.is_trimmed(&manager));

        let node = node.canonicalize(&manager);
        assert!(node.is_trimmed(&manager));
        assert_eq!(
            node,
            create_literal(Literal::new(Polarity::Positive, "A", 0))
        );
    }

    #[test]
    fn not_trimmed_complex() {
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let element_1 = Element {
            prime: (pos_a.id()),
            sub: (Sdd::new_true().id()),
        };

        let neg_a = create_literal(Literal::new(Polarity::Negative, "A", 0));
        let element_2 = Element {
            prime: (neg_a.id()),
            sub: (Sdd::new_false().id()),
        };

        // // Decomposition `{(A, true), (!A, false)}`.
        let decision = Decision {
            elements: btreeset!(element_1, element_2),
        };
        let sdd = Sdd::new(SddType::Decision(decision), 0, None);

        let decisions = &vec![sdd.clone(), neg_a, pos_a];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager
            .get_node(sdd.id())
            .expect("node is not present in the unique table");
        assert!(!node.is_trimmed(&manager));

        let node = node.canonicalize(&manager);
        assert!(node.is_trimmed(&manager));
        assert_eq!(
            node,
            create_literal(Literal::new(Polarity::Positive, "A", 0))
        );
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B", 1));
        let element_1_1 = Element {
            prime: Sdd::new_true().id(),
            sub: neg_b.id(),
        };

        // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
        let decision_1 = Decision {
            elements: btreeset!(element_1_1),
        };

        let sdd_1 = Sdd::new(SddType::Decision(decision_1), 0, None);

        let pos_a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let element_2_1 = Element {
            prime: pos_a.id(),
            sub: Sdd::new_true().id(),
        };

        let element_2_2 = Element {
            prime: sdd_1.id(),
            sub: Sdd::new_false().id(),
        };

        // // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
        let decision_2 = Decision {
            elements: btreeset!(element_2_1, element_2_2),
        };

        let sdd_2 = Sdd::new(SddType::Decision(decision_2), 0, None);
        let decisions = &vec![sdd_1.clone(), sdd_2.clone(), pos_a, neg_b];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);
        let node = manager
            .get_node(sdd_2.id())
            .expect("node is not present in the unique table");
        assert!(!node.is_trimmed(&manager));
        assert!(!sdd_1.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_complex() {
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let element_1 = Element {
            prime: pos_a.id(),
            sub: Sdd::new_true().id(),
        };

        let element_2 = Element {
            prime: pos_a.id(),
            sub: Sdd::new_false().id(),
        };

        // Decomposition `{(A, true), (B, false)}`.
        let decision = Decision {
            elements: btreeset!(element_1, element_2),
        };
        let sdd = Sdd::new(SddType::Decision(decision), 0, None);
        let decisions = &vec![sdd.clone(), pos_a];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition {(A, true), (B, false)} is trimmed.
        let node = manager
            .get_node(sdd.id())
            .expect("node is not present in the unique table");
        assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B", 1));
        let element_1_1 = Element {
            prime: (neg_b.id()),
            sub: (Sdd::new_true().id()),
        };

        // Decomposition `{(!B, true)}`.
        let decision_1 = Decision {
            elements: btreeset!(element_1_1),
        };
        let sdd_1 = Sdd::new(SddType::Decision(decision_1), 0, None);

        let pos_a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let element_2_1 = Element {
            prime: pos_a.id(),
            sub: Sdd::new_true().id(),
        };
        let element_2_2 = Element {
            prime: sdd_1.id(),
            sub: Sdd::new_false().id(),
        };

        // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
        let decision_2 = Decision {
            elements: btreeset!(element_2_1, element_2_2),
        };
        let sdd_2 = Sdd::new(SddType::Decision(decision_2), 0, None);
        let decisions = &vec![sdd_1, sdd_2.clone(), pos_a, neg_b];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        let node = manager
            .get_node(sdd_2.id())
            .expect("node is not present in the unique table");
        assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn not_compressed() {
        // TODO: Test compression once disjunction actually works.
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B", 1));
        let element_1 = Element {
            prime: Sdd::new_true().id(),
            sub: neg_b.id(),
        };

        let element_2 = Element {
            prime: pos_a.id(),
            sub: neg_b.id(),
        };

        // Decomposition `{(true, !B), (A, !B)}` is not compressed due to identical subs.
        let decision_1 = Decision {
            elements: btreeset!(element_1, element_2),
        };
        let sdd = Sdd::new(SddType::Decision(decision_1), 0, None);
        let decisions = &vec![sdd.clone(), pos_a, neg_b];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        assert!(!sdd.is_compressed(&manager));
    }

    #[test]
    fn compressed() {
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A", 0));
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B", 1));
        let element_1 = Element {
            prime: Sdd::new_true().id(),
            sub: neg_b.id(),
        };

        let element_2 = Element {
            prime: pos_a.id(),
            sub: Sdd::new_true().id(),
        };

        // Decomposition `{(true, !B), (A, true)}` is compressed.
        let decision_1 = Decision {
            elements: btreeset!(element_1, element_2),
        };

        let sdd = Sdd::new(SddType::Decision(decision_1), 0, None);
        let decisions = &vec![sdd.clone(), pos_a, neg_b];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        assert!(sdd.is_compressed(&manager));
    }

    #[test]
    fn vtree_dependence() {
        let manager = SddManager::new(SddOptions::default());
        let a = manager.literal("A", Polarity::Positive);
        manager.literal("B", Polarity::Positive);
        let c = manager.literal("C", Polarity::Positive);
        let d = manager.literal("D", Polarity::Positive);
        // The vtree looks like this:
        //   (1)
        //   / \
        //  A  (3)
        //     / \
        //    B  (5)
        //       / \
        //      C   D

        let c_and_d = manager.conjoin(&c, &d);
        assert_eq!(manager.model_count(&c_and_d), 4); // Sanity check

        let c_and_d_and_a = manager.conjoin(&c_and_d, &a);
        assert_eq!(manager.model_count(&c_and_d_and_a), 2); // Sanity check

        let root = manager.root().unwrap();

        // `c && d && a` must be normalized for root.
        assert_eq!(c_and_d_and_a.vtree_idx, root.borrow().get_index());

        let dep = c_and_d_and_a.dependence_on_left_vtree(&root, &manager);
        assert_eq!(dep, LeftDependence::A);

        // TODO: Test dependencies more - try to capture all possible cases.
    }
}
