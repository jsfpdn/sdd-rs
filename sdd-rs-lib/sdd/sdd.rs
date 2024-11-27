use bitvec::vec::BitVec;
use core::fmt;
use derive_more::derive::AddAssign;
use std::{collections::BTreeSet, fmt::Display};

use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::{Literal, Variable},
    manager::{SddManager, FALSE_SDD_IDX, TRUE_SDD_IDX},
    sdd::{Decision, Element, SddRef},
    vtree::{LeftDependence, Node, RightDependence, VTreeIdx, VTreeRef},
};

#[derive(Eq, PartialEq, Hash, Debug, PartialOrd, Ord, Clone, Copy, AddAssign)]
pub struct SddId(pub u32);

impl Display for SddId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SddIdx({})", self.0)
    }
}

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

// TODO: Sdd should become public only within the crate.
#[derive(PartialEq, Eq, Clone)]
pub struct Sdd {
    pub(crate) sdd_idx: SddId,
    pub(crate) sdd_type: SddType,
    pub(crate) vtree: VTreeRef,
    pub(crate) negation: Option<SddId>,
    pub(crate) model_count: Option<u64>,
    pub(crate) models: Option<Vec<BitVec>>,
}

impl fmt::Debug for Sdd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sdd")
            .field("sdd_type", &self.sdd_type)
            .field("vtree_idx", &self.vtree.index())
            .field("id", &self.id())
            .finish()
    }
}

impl Dot for Sdd {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager) {
        match self.sdd_type.clone() {
            // Do not render literals and constants as they do not provide any
            // value and only take up space.
            SddType::True | SddType::False | SddType::Literal(..) => (),
            SddType::Decision(node) => {
                let idx = node.hash();
                for elem in node.elements.iter() {
                    elem.draw(writer, manager);
                    writer.add_edge(Edge::Simple(idx, elem.hash()));
                }
                let node_type =
                    NodeType::Circle(self.vtree.index().0 as u16, Some(self.id().0 as usize));
                writer.add_node(idx, node_type);
            }
        };
    }
}

impl Sdd {
    #[must_use]
    pub(crate) fn new(
        sdd_type: SddType,
        sdd_idx: SddId,
        vtree: VTreeRef,
        negation: Option<SddId>,
    ) -> Sdd {
        let (model_count, models) = match sdd_type.clone() {
            SddType::False => (Some(0), None),
            SddType::True => (Some(1), None),
            SddType::Literal(_) => (Some(1), None),
            _ => (None, None),
        };

        Sdd {
            sdd_idx,
            sdd_type,
            vtree,
            negation,
            model_count,
            models,
        }
    }

    #[must_use]
    pub(crate) fn new_true() -> Sdd {
        Self::new(
            SddType::True,
            TRUE_SDD_IDX,
            VTreeRef::new(None, VTreeIdx(0), Node::Leaf(Variable::new("True", 0))),
            None,
        )
    }

    #[must_use]
    pub(crate) fn new_false() -> Sdd {
        Self::new(
            SddType::False,
            FALSE_SDD_IDX,
            VTreeRef::new(None, VTreeIdx(0), Node::Leaf(Variable::new("True", 0))),
            None,
        )
    }

    #[must_use]
    pub fn id(&self) -> SddId {
        self.sdd_idx
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
                    sub: sub.negate(manager).clone(),
                });
            }

            let negated_sdd = manager.new_sdd_from_type(
                SddType::Decision(Decision { elements }),
                self.vtree.clone(),
                Some(self.id()),
            );

            // Cache the negation for this SDD.
            self.negation = Some(negated_sdd.id());
            return negated_sdd;
        }

        match self.sdd_type {
            SddType::True => manager.contradiction(),
            SddType::False => manager.tautology(),
            SddType::Literal(ref literal) => {
                manager.literal(&literal.var_label().label(), !literal.polarity())
            }
            SddType::Decision(..) => {
                panic!("cannot happen - bug in the if expression's condition")
            }
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
                    trimmed_sdd.0.borrow().clone()
                } else {
                    let decision = decision.compress(manager);
                    if let Some(trimmed_sdd) = decision.trim(manager) {
                        trimmed_sdd.0.borrow().clone()
                    } else {
                        Sdd::new(
                            SddType::Decision(decision.clone()),
                            self.sdd_idx,
                            self.vtree.clone(),
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
    pub(crate) fn unique_d(
        gamma: BTreeSet<Element>,
        vtree: VTreeRef,
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

        manager.new_sdd_from_type(
            SddType::Decision(Decision { elements: gamma }),
            vtree.clone(),
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
    #[allow(unused)]
    pub(crate) fn dependence_on_left_vtree(
        &self,
        w: &VTreeRef,
        manager: &SddManager,
    ) -> LeftDependence {
        let SddType::Decision(ref decision) = self.sdd_type else {
            panic!("cannot get dependence on anything other than decision node");
        };

        let primes = decision.primes().to_vec();
        // No need to filter out constants from collected primes since they cannot
        // occur as primes of elements.

        let mut depends_on_a = false;
        let mut depends_on_b = false;
        let w_idx = w.index();

        for prime in &primes {
            assert!(!prime.is_constant());

            if prime.vtree().index() == w_idx {
                return LeftDependence::AB;
            }

            if prime.vtree().index() < w_idx {
                depends_on_a = true;
            } else {
                depends_on_b = true;
            }

            if depends_on_a && depends_on_b {
                return LeftDependence::AB;
            }
        }

        assert!(depends_on_a || depends_on_b);
        assert!(!(depends_on_a && depends_on_b));

        if depends_on_a {
            return LeftDependence::A;
        }

        LeftDependence::B
    }

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
            if sub.vtree().index() == x_idx {
                return RightDependence::BC;
            }

            if sub.vtree().index() < x_idx {
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

    pub(crate) fn invalidate_cache(&mut self) {
        tracing::debug!(sddId = self.id().0, "invalidating cache");
        self.models = None;
        self.model_count = None;
    }
}

#[cfg(test)]
mod test {
    use crate::literal::Polarity;
    use crate::manager::options::{vars, VTreeStrategy};
    use crate::manager::{options::SddOptions, SddManager};
    use crate::vtree::LeftDependence;

    #[test]
    fn vtree_dependence() {
        let options = SddOptions::builder()
            .variables(vars(vec!["A", "B", "C", "D"]))
            .vtree_strategy(VTreeStrategy::RightLinear)
            .build();
        let manager = SddManager::new(options);

        let a = manager.literal("A", Polarity::Positive);
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
        assert_eq!(c_and_d_and_a.vtree().index(), root.index());

        let dep = c_and_d_and_a
            .0
            .borrow()
            .dependence_on_left_vtree(&root, &manager);
        assert_eq!(dep, LeftDependence::A);

        // TODO: Test dependencies more - try to capture all possible cases.
    }
}
