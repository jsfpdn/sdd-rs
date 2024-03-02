use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;

use crate::literal::Literal;
use crate::manager::SddManager;

#[cfg(test)]
#[path = "./sdd_test.rs"]
mod sdd_test;

type NodeIndex = u64;

#[derive(PartialEq, Eq, Clone, Hash)]
pub struct Node {
    sdd: Sdd,

    // Index of the parent node in the SDDManager.nodes vector.
    parent: Option<NodeIndex>,
    index: NodeIndex, // index == sdd::hash
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

    fn as_element(&self) -> &SddAnd {
        match self {
            Sdd::Element(elem) | Sdd::ElementCompl(elem) => elem,
            _ => panic!("Cannot cast to element!"),
        }
    }

    fn as_decision(&self) -> &SddOr {
        match self {
            Sdd::Decision(decision) | Sdd::DecisionCompl(decision) => decision,
            _ => panic!("Cannot cast to decision!"),
        }
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
    elements: BTreeSet<NodeIndex>,
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
            let element = manager.get_node(element_idx).unwrap().sdd.as_element();
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
            let element = manager.get_node(element_idx).unwrap().sdd.as_element();
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
    /// SDD is trimmed by traversing bottom up, replacing decompositions {(true, alpha)} and {(alpha, true), (!alpha, false)} with alpha.
    /// SDD is decompressed by repeatedly replacing elements `(p, s)` and `(q, s)` with
    /// `(p || q, s)`.
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
