use super::SddId;
use crate::{
    manager::SddManager,
    sdd::{element::Element, SddRef},
};
use std::collections::{BTreeSet, HashSet};

/// Decision represents an X-partition: a set of elements (conjunctions)
/// maintaining the strong determinism and (X,Y)-decomposition properties.
#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) struct Decision {
    pub(crate) elements: BTreeSet<Element>,
}

impl Decision {
    /// Recursivelly checks whether the decision node is trimmed.
    /// Decision node is `trimmed` if it does not contain decompositions of the form `{(True, A)}` or
    /// `{(A, True), (!A, False)}`.
    ///
    /// See definition 8 in [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    #[must_use]
    pub(crate) fn is_trimmed(&self, manager: &SddManager) -> bool {
        let mut primes: HashSet<SddId> = HashSet::new();

        if self.elements.len() >= 3 {
            return true;
        }

        for element in &self.elements {
            let (prime, sub) = element.get_prime_sub();

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
            if primes.contains(&prime.id()) {
                return false;
            }

            primes.insert(prime.negate(manager).id());
        }

        // Check that elements are also trimmed.
        self.elements.iter().all(|el| el.is_trimmed(manager))
    }

    /// Recursivelly checks whether the decision node is compressed.
    /// Decision node is compressed if all subs are distinct, i.e., for all indexes i,j such that i != j,
    /// it holds that `s_i != s_j`.
    ///
    /// See definition 8 in [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    #[must_use]
    pub(super) fn is_compressed(&self, manager: &SddManager) -> bool {
        let mut subs: HashSet<SddId> = HashSet::new();
        for element in &self.elements {
            let (_, sub) = element.get_prime_sub();
            if subs.contains(&sub.id()) {
                return false;
            }

            subs.insert(sub.id());
        }

        // Check that all elements are also compressed.
        self.elements.iter().all(|el| el.is_compressed(manager))
    }

    /// Trim decision node by replacing decompositions {(true, alpha)}
    /// and {(alpha, true), (!alpha, false)} with alpha. Returns a Boolean
    /// denoting whether the decision node had to be trimmed.
    pub(super) fn trim(&self, manager: &SddManager) -> Option<SddRef> {
        let elements: Vec<&Element> = self.elements.iter().collect();
        if self.elements.len() == 1 {
            let el = elements.first().unwrap();
            if el.prime.is_true() {
                return Some(el.sub.clone());
            }
        }

        if self.elements.len() == 2 {
            let el_1 = elements.first().unwrap();
            let el_2 = elements.get(1).unwrap();

            let el_1_prime;
            let el_2_prime;
            if el_1.sub.is_true() && el_2.sub.is_false() {
                // Check for {(_, true), (_, false)}.
                el_1_prime = &el_1.prime;
                el_2_prime = &el_2.prime;
            } else if el_2.sub.is_true() && el_1.sub.is_false() {
                // Check for {(_, false), (_, true)}.
                el_1_prime = &el_2.prime;
                el_2_prime = &el_1.prime;
            } else {
                return None;
            }

            if el_1_prime.eq_negated(el_2_prime, manager) {
                return Some(el_1_prime.clone());
            }
        }

        None
    }

    /// Compress decision node by repeatedly replacing elements
    /// `(p, s)` and `(q, s)` with `(p || q, s)`.
    pub(super) fn compress(&self, manager: &SddManager) -> Decision {
        let mut elements: Vec<_> = self.elements.iter().cloned().collect();
        let mut last_el_idx = self.elements.len() - 1;
        let mut i = 0;

        while i < last_el_idx {
            let mut j = i + 1;

            let mut fst = elements.get(i).unwrap().clone();
            while j <= last_el_idx {
                let snd = elements.get(j).unwrap();
                if fst.sub != snd.sub {
                    j += 1;
                    continue;
                }

                // The subs are equal, we can compress the elements together.
                let new_prime = manager.disjoin(&fst.prime, &snd.prime);

                fst = Element {
                    prime: new_prime,
                    sub: fst.sub,
                };
                elements[i] = fst.clone();

                // Remove element at the `j`-th position from the vector of elements.
                // This means decreasing the `last_el_idx` and not moving the `j` index
                // since there will be a new element from the back of the vector which
                // we can process in the next iteration of this inner loop.
                elements.swap_remove(j);
                last_el_idx -= 1;
                continue;
            }

            i += 1;
        }

        Decision {
            elements: elements.iter().cloned().collect(),
        }
    }

    /// Get all primes of a decision node.
    pub(super) fn primes(&self) -> Vec<SddRef> {
        self.elements
            .iter()
            .map(|Element { prime, .. }| prime)
            .cloned()
            .collect()
    }

    /// Get all subs of a decision node.
    pub(super) fn subs(&self) -> Vec<SddRef> {
        self.elements
            .iter()
            .map(|Element { sub, .. }| sub)
            .cloned()
            .collect()
    }

    /// Compute the hash of a decision node. This is supposed to
    /// be used only for drawing Graphviz graphs.
    pub(crate) fn hash(&self) -> usize {
        let elements: BTreeSet<(SddId, SddId)> = self
            .elements
            .iter()
            .map(|Element { prime, sub }| (prime.id(), sub.id()))
            .collect();
        fxhash::hash(&elements)
    }
}
