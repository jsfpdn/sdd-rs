use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;

use crate::literal::Literal;
use crate::manager::SddManager;

#[cfg(test)]
#[path = "./sdd_test.rs"]
mod sdd_test;

#[derive(PartialEq, Eq, Clone)]
pub struct Node {
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

#[derive(PartialEq, Eq, Clone, Hash)]
pub struct Decision {
    elements: BTreeSet<Element>,
}

// Element node (a paired box) is a conjunction of prime and sub.
#[derive(PartialEq, Eq, Clone, Hash, Copy, PartialOrd, Ord)]
pub struct Element {
    prime: Box,
    sub: Box,
}

impl Element {
    fn is_trimmed(&self, manager: &SddManager) -> bool {
        self.prime.is_trimmed(manager) && self.sub.is_trimmed(manager)
    }

    fn is_compressed(&self, manager: &SddManager) -> bool {
        self.prime.is_compressed(manager) && self.sub.is_compressed(manager)
    }
}

type NodeIndex = u64;

#[derive(PartialEq, Eq, Clone, Hash, Copy, PartialOrd, Ord)]
pub enum Box {
    True,
    False,
    Literal(Literal),
    DecisionRegular(NodeIndex),
    DecisionComplement(NodeIndex),
}

impl Box {
    fn is_true(&self) -> bool {
        matches!(self, Box::True)
    }

    fn is_false(&self) -> bool {
        matches!(self, Box::False)
    }

    fn is_constant(&self) -> bool {
        self.is_true() || self.is_false()
    }

    fn negate(&self) -> Box {
        match self {
            Box::True => Box::False,
            Box::False => Box::True,
            Box::Literal(literal) => Box::Literal(literal.negate()),
            Box::DecisionRegular(decision) => Box::DecisionComplement(decision.to_owned()),
            Box::DecisionComplement(decision) => Box::DecisionRegular(decision.to_owned()),
        }
    }

    fn is_trimmed(&self, manager: &SddManager) -> bool {
        match self {
            Box::True | Box::False | Box::Literal(_) => true,
            Box::DecisionRegular(decision_idx) | Box::DecisionComplement(decision_idx) => manager
                .get_node(decision_idx)
                .unwrap()
                .decision
                .is_trimmed(manager),
        }
    }

    fn is_compressed(&self, manager: &SddManager) -> bool {
        match self {
            Box::True | Box::False | Box::Literal(_) => true,
            Box::DecisionRegular(decision_idx) | Box::DecisionComplement(decision_idx) => manager
                .get_node(decision_idx)
                .unwrap()
                .decision
                .is_compressed(manager),
        }
    }
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
    pub fn is_trimmed(&self, manager: &SddManager) -> bool {
        let mut primes: HashSet<Box> = HashSet::new();

        if self.elements.len() >= 3 {
            return true;
        }

        for element in &self.elements {
            // Check for `{(true, A)}`.
            if element.prime.is_true() {
                return false;
            }

            // Check for elements `(A, True)` and `(!A, False)`. We can continue with the next iteration
            // if the sub is not True or False.
            if !element.sub.is_constant() {
                continue;
            }

            // Check whether we have already seen this literal but negated.
            if primes.contains(&element.prime) {
                return false;
            }

            primes.insert(element.prime.negate());
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
    pub fn is_compressed(&self, manager: &SddManager) -> bool {
        let mut subs: HashSet<Box> = HashSet::new();
        for element in &self.elements {
            if subs.contains(&element.sub) {
                return false;
            }

            subs.insert(element.sub);
        }

        // Check that all elements are also compressed.
        self.elements.iter().all(|el| el.is_compressed(manager))
    }

    /// Recursivelly trims and compresses SDD.
    ///
    /// SDD is trimmed by traversing bottom up, replacing decompositions {(true, alpha)} and {(alpha, true), (!alpha, false)} with alpha.
    /// SDD is decompressed by repeatedly replacing elements `(p, s)` and `(q, s)` with
    /// `(p || q, s)`.
    pub fn trim_and_compress(&mut self) {
        todo!("Implement me!")
    }
}
