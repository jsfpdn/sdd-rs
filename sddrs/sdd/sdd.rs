use bitvec::vec::BitVec;
use core::fmt;
use derive_more::derive::AddAssign;
use std::{collections::BTreeSet, fmt::Display};

use crate::{
    btreeset,
    literal::{Literal, Variable},
    manager::{CachedOperation, SddManager, FALSE_SDD_IDX, TRUE_SDD_IDX},
    sdd::{Decision, Element, SddRef},
    vtree::{LeftDependence, Node, RightDependence, VTreeIdx, VTreeRef},
};

/// [`SddId`] is a unique ID of an SDD.
#[allow(clippy::module_name_repetitions)]
#[derive(Eq, PartialEq, Hash, Debug, PartialOrd, Ord, Clone, Copy, AddAssign)]
pub struct SddId(pub u32);

impl Display for SddId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SddIdx({})", self.0)
    }
}

/// An SDD node can be either a terminal (constant or literal)
/// or a decision node.
#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) enum SddType {
    True,
    False,
    Literal(Literal),
    Decision(Decision),
}

impl SddType {
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

/// [`Sdd`] is the main structure encompassing all relevant
/// information about an SDD node.
#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) struct Sdd {
    pub(crate) id: SddId,
    #[allow(clippy::struct_field_names)]
    pub(crate) sdd_type: SddType,
    pub(crate) vtree: VTreeRef,
    pub(crate) model_count: Option<u64>,
    pub(crate) models: Option<Vec<BitVec>>,
}

impl Sdd {
    /// Create a new [`Sdd`].
    #[must_use]
    pub(crate) fn new(sdd_type: SddType, id: SddId, vtree: VTreeRef) -> Sdd {
        let (model_count, models) = match sdd_type.clone() {
            SddType::False => (Some(0), None),
            SddType::True | SddType::Literal(..) => (Some(1), None),
            SddType::Decision(..) => (None, None),
        };

        Sdd {
            id,
            sdd_type,
            vtree,
            model_count,
            models,
        }
    }

    /// Create a new [`Sdd`] representing `true`.
    #[must_use]
    pub(crate) fn new_true() -> Sdd {
        Self::new(
            SddType::True,
            TRUE_SDD_IDX,
            VTreeRef::new(None, VTreeIdx(0), Node::Leaf(Variable::new("True", 0))),
        )
    }

    /// Create a new [`Sdd`] representing `false`.
    #[must_use]
    pub(crate) fn new_false() -> Sdd {
        Self::new(
            SddType::False,
            FALSE_SDD_IDX,
            VTreeRef::new(None, VTreeIdx(0), Node::Leaf(Variable::new("True", 0))),
        )
    }

    #[must_use]
    pub(crate) fn id(&self) -> SddId {
        self.id
    }

    /// Check whether the SDD represents a literal.
    pub(crate) fn is_literal(&self) -> bool {
        matches!(
            self,
            Sdd {
                sdd_type: SddType::Literal(_literal),
                ..
            }
        )
    }

    /// Expand the SDD into a decision node as described in Algorithm 1 in
    /// [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    pub(crate) fn expand(&self, manager: &SddManager) -> Decision {
        match self.sdd_type {
            SddType::True => Decision {
                elements: btreeset!(Element {
                    prime: manager.tautology(),
                    sub: manager.tautology(),
                }),
            },
            SddType::False => Decision {
                elements: btreeset!(Element {
                    prime: manager.tautology(),
                    sub: manager.contradiction(),
                }),
            },
            SddType::Literal(_) => Decision {
                elements: btreeset!(Element {
                    prime: manager.get_node(self.id()),
                    sub: manager.contradiction(),
                }),
            },
            SddType::Decision(ref dec) => dec.clone(),
        }
    }

    /// Negate the SDD and cache it.
    pub(crate) fn negate(&mut self, manager: &SddManager) -> SddRef {
        if let SddType::Decision(ref dec) = self.sdd_type {
            let mut elements = BTreeSet::new();
            for Element { prime, sub } in &dec.elements {
                elements.insert(Element {
                    prime: prime.clone(),
                    sub: sub.negate(manager),
                });
            }

            let negated_sdd = manager.new_sdd_from_type(
                SddType::Decision(
                    Decision {
                        elements: elements.clone(),
                    }
                    .compress(manager),
                ),
                self.vtree.clone(),
                Some(self.id()),
            );

            debug_assert!(negated_sdd.is_compressed(manager));
            debug_assert!(negated_sdd.is_trimmed(manager));

            // Cache the negation for this SDD.
            manager.cache_operation(&CachedOperation::Neg(self.id()), negated_sdd.id());
            return negated_sdd;
        }

        match self.sdd_type {
            SddType::True => manager.contradiction(),
            SddType::False => manager.tautology(),
            SddType::Literal(ref literal) => manager
                .literal(&literal.var_label().label(), !literal.polarity())
                .unwrap(),
            SddType::Decision(..) => {
                panic!("cannot happen - bug in the if expression's condition")
            }
        }
    }

    /// Recursively check whether [`self`] and all its descendants are trimmed.
    /// SDD is trimmed if it does not contain decompositions in the form of
    /// `{(true, alpha)}` and `{(alpha, true), (!alpha, false)}`.
    pub fn is_trimmed(&self, manager: &SddManager) -> bool {
        match self.sdd_type {
            SddType::True | SddType::False | SddType::Literal(_) => true,
            SddType::Decision(ref decision) => decision.is_trimmed(manager),
        }
    }

    /// Recursively check whether [`self`] and all its descendants are compressed.
    /// SDD is compressed if no elements share a sub.
    pub fn is_compressed(&self, manager: &SddManager) -> bool {
        match self.sdd_type {
            SddType::True | SddType::False | SddType::Literal(_) => true,
            SddType::Decision(ref decision) => decision.is_compressed(manager),
        }
    }

    /// Canonicalize SDD by trimming and compressing it. Only decision nodes can
    /// be canonicalized. Returns the SDD and flag whether it had to be canonicalized or not.
    ///
    /// Decision node is trimmed by replacing decompositions {(true, alpha)}
    /// and {(alpha, true), (!alpha, false)} with alpha. SDD is compressed by repeatedly
    /// replacing elements `(p, s)` and `(q, s)` with `(p || q, s)`.
    #[must_use]
    pub(crate) fn canonicalize(&self, manager: &SddManager) -> SddRef {
        match &self.sdd_type {
            SddType::Decision(decision) => {
                if let Some(trimmed_sdd) = decision.trim(manager) {
                    trimmed_sdd.clone()
                } else {
                    let decision = decision.compress(manager);
                    if let Some(trimmed_sdd) = decision.trim(manager) {
                        trimmed_sdd.clone()
                    } else {
                        SddRef::new(Sdd::new(
                            SddType::Decision(decision.clone()),
                            self.id,
                            self.vtree.clone(),
                        ))
                    }
                }
            }
            _ => panic!("unexpected sdd_type"),
        }
    }

    /// Compute "uniqueD" SDD as described in Algorithm 1 in
    /// [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    pub(crate) fn unique_d(
        gamma: &BTreeSet<Element>,
        vtree: &VTreeRef,
        manager: &SddManager,
    ) -> SddRef {
        // gamma == {(T, T)}?
        if gamma.eq(&btreeset![Element {
            prime: manager.tautology(),
            sub: manager.tautology(),
        }]) {
            return manager.tautology();
        }

        // gamma == {(T, F)}?
        if gamma.eq(&btreeset![Element {
            prime: manager.tautology(),
            sub: manager.contradiction(),
        }]) {
            return manager.contradiction();
        }

        let sdd = SddRef::new(Sdd::new(
            SddType::Decision(Decision {
                elements: gamma.clone(),
            }),
            manager.idx(),
            vtree.clone(),
        ));
        manager.move_idx();
        sdd
    }

    /// Get the representation of the SDD for the .DOT format.
    pub(super) fn dot_repr(&self) -> String {
        match self.sdd_type.clone() {
            SddType::True => String::from("⊤"),
            SddType::False => String::from("⊥"),
            SddType::Literal(literal) => format!("{literal}"),
            SddType::Decision(..) => String::new(),
        }
    }

    /// Get for which vtrees are primes of this Sdd normalized.
    /// See [`LeftDependence`] for more information.
    ///
    /// # Panics
    ///
    /// The function panics if [`self`] is anything other than [`SddType::Decision`].
    #[must_use]
    #[allow(unused)]
    pub(crate) fn dependence_on_left_vtree(
        &self,
        w: &VTreeRef,
        manager: &SddManager,
    ) -> LeftDependence {
        let SddType::Decision(ref decision) = self.sdd_type else {
            panic!("cannot get dependence on anything other than decision node");
        };

        let primes = decision.primes().clone();
        // No need to filter out constants from collected primes since they cannot
        // occur as primes of elements.

        let mut depends_on_a = false;
        let mut depends_on_b = false;
        let w_idx = w.index();

        for prime in &primes {
            // TODO: This is where the bug probably manifests itself.
            // assert!(!prime.is_true());
            // assert!(!prime.is_false());
            // The following condidition should be removed and the
            // asserts uncommented.
            if prime.is_constant() {
                continue;
            }

            if prime.vtree().unwrap().index() == w_idx {
                return LeftDependence::AB;
            }

            if prime.vtree().unwrap().index() < w_idx {
                depends_on_a = true;
            } else {
                depends_on_b = true;
            }

            if depends_on_a && depends_on_b {
                return LeftDependence::AB;
            }
        }

        // TODO: This assertion should be put back.
        // assert!(depends_on_a || depends_on_b);
        // assert!(!(depends_on_a && depends_on_b));

        if depends_on_a {
            return LeftDependence::A;
        }

        LeftDependence::B
    }

    /// Get for which vtrees are subs of this Sdd normalized.
    /// See [`RightDependence`] for more information.
    ///
    /// # Panics
    ///
    /// The function panics if [`self`] is anything other than [`SddType::Decision`].
    #[must_use]
    #[allow(unused)]
    pub(crate) fn dependence_on_right_vtree(
        &self,
        x: &VTreeRef,
        manager: &SddManager,
    ) -> RightDependence {
        let SddType::Decision(ref decision) = self.sdd_type else {
            panic!("cannot get dependence on anything other than decision node");
        };

        let subs: Vec<_> = decision
            .subs()
            .iter()
            .filter(|sub| !sub.is_constant())
            .cloned()
            .collect();

        let mut depends_on_b = false;
        let mut depends_on_c = false;
        let x_idx = x.index();

        for sub in &subs {
            if sub.vtree().unwrap().index() == x_idx {
                return RightDependence::BC;
            }

            if sub.vtree().unwrap().index() < x_idx {
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

    /// Invalidate cached models and model counts.
    /// TODO: Check whether this can be removed.
    pub(crate) fn invalidate_cache(&mut self) {
        tracing::debug!(sddId = self.id().0, "invalidating cache");
        self.models = None;
        self.model_count = None;
    }
}

#[cfg(test)]
mod test {
    use crate::literal::Polarity;
    use crate::manager::options::VTreeStrategy;
    use crate::manager::{options::SddOptions, SddManager};
    use crate::vtree::LeftDependence;

    use bon::arr;

    #[test]
    fn vtree_dependence() {
        let options = SddOptions::builder()
            .variables(arr!["A", "B", "C", "D"])
            .vtree_strategy(VTreeStrategy::RightLinear)
            .build();
        let manager = SddManager::new(&options);

        let a = manager.literal("A", Polarity::Positive).unwrap();
        let c = manager.literal("C", Polarity::Positive).unwrap();
        let d = manager.literal("D", Polarity::Positive).unwrap();
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

        let root = manager.root();

        // `c && d && a` must be normalized for root.
        assert_eq!(c_and_d_and_a.vtree().unwrap().index(), root.index());

        let dep = c_and_d_and_a
            .0
            .borrow()
            .dependence_on_left_vtree(&root, &manager);
        assert_eq!(dep, LeftDependence::A);
    }
}
