use core::fmt;
use std::{collections::BTreeSet, hash::Hash};

use bitvec::vec::BitVec;

use crate::{
    btreeset,
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::Literal,
    manager::{SddManager, FALSE_SDD_IDX, TRUE_SDD_IDX},
    sdd::{Decision, Element, SddRef},
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

// TODO: Sdd should become public only within the crate.
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
    pub(crate) fn new(
        sdd_type: SddType,
        sdd_idx: u16,
        vtree_idx: u16,
        negation: Option<usize>,
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
            vtree_idx,
            negation,
            model_count,
            models,
        }
    }

    #[must_use]
    pub(crate) fn new_true() -> Sdd {
        Self::new(SddType::True, TRUE_SDD_IDX, 0, None)
    }

    #[must_use]
    pub(crate) fn new_false() -> Sdd {
        Self::new(SddType::False, FALSE_SDD_IDX, 0, None)
    }

    #[must_use]
    pub fn id(&self) -> usize {
        // TODO: change the type to u{16,32,64}.
        self.sdd_idx as usize
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
                    prime: TRUE_SDD_IDX as usize,
                    sub: TRUE_SDD_IDX as usize,
                }),
            },
            SddType::False => Decision {
                elements: btreeset!(Element {
                    prime: TRUE_SDD_IDX as usize,
                    sub: FALSE_SDD_IDX as usize,
                }),
            },
            SddType::Literal(_) => Decision {
                elements: btreeset!(Element {
                    prime: self.id(),
                    sub: FALSE_SDD_IDX as usize,
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
                let sub = manager.get_node(*sub).unwrap().negate(manager);

                elements.insert(Element {
                    prime: *prime,
                    sub: sub.id(),
                });
            }

            let negated_sdd = manager.new_sdd_from_type(
                SddType::Decision(Decision { elements }),
                self.vtree_idx,
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
                    trimmed_sdd.0.borrow().clone()
                } else {
                    let decision = decision.compress(manager);
                    if let Some(trimmed_sdd) = decision.trim(manager) {
                        trimmed_sdd.0.borrow().clone()
                    } else {
                        Sdd::new(
                            SddType::Decision(decision.clone()),
                            self.sdd_idx,
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
    pub(crate) fn unique_d<'b>(
        gamma: BTreeSet<Element>,
        vtree_idx: u16,
        manager: &SddManager,
    ) -> Sdd {
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
            0, // TODO: Double check this in the caller that we are setting this properly.
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

        let primes: Vec<_> = decision.primes(&manager).iter().cloned().collect();
        // No need to filter out constants from collected primes since they cannot
        // occur as primes of elements.

        let mut depends_on_a = false;
        let mut depends_on_b = false;
        let w_idx = w.borrow().get_index();

        for prime in &primes {
            if prime.vtree_idx() == w_idx {
                return LeftDependence::AB;
            }

            if prime.vtree_idx() < w_idx {
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

        let subs: Vec<_> = decision
            .subs(&manager)
            .iter()
            .filter(|sub| !sub.is_constant())
            .cloned()
            .collect();

        let mut depends_on_b = false;
        let mut depends_on_c = false;
        let x_idx = x.borrow().get_index();

        for sub in &subs {
            if sub.vtree_idx() == x_idx {
                return RightDependence::BC;
            }

            if sub.vtree_idx() < x_idx {
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
    use crate::literal::Polarity;
    use crate::manager::{options::SddOptions, SddManager};
    use crate::sdd::LeftDependence;

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
        assert_eq!(c_and_d_and_a.vtree_idx(), root.borrow().get_index());

        let dep = c_and_d_and_a
            .0
            .borrow()
            .dependence_on_left_vtree(&root, &manager);
        assert_eq!(dep, LeftDependence::A);

        // TODO: Test dependencies more - try to capture all possible cases.
    }
}
