use core::fmt;
use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;

use crate::btreeset;
use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::Literal,
    manager::SddManager,
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
    pub(crate) prime: usize,
    pub(crate) sub: usize,
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
            manager.get_node(self.prime).expect(
                format!(
                    "element_prime with id {} not present in unique_table",
                    self.prime
                )
                .as_str(),
            ),
            manager.get_node(self.sub).expect(
                format!(
                    "element_sub with id {} not present in unique_table",
                    self.sub
                )
                .as_str(),
            ),
        )
    }
}

impl Dot for Element {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager) {
        let idx = fxhash::hash(self);

        let (prime, sub) = self.get_prime_sub(manager);

        writer.add_node(idx, NodeType::Record(prime.dot_repr(), sub.dot_repr()));

        if let Sdd {
            sdd_type: SddType::Decision(node),
            ..
        } = manager
            .get_node(self.prime)
            .expect("element_prime not present in unique_table")
        {
            writer.add_edge(Edge::Prime(idx, fxhash::hash(&node)));
        }
        if let Sdd {
            sdd_type: SddType::Decision(node),
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
    pub(crate) sdd_type: SddType,
    pub(crate) vtree_idx: u16,
    pub(crate) negation: Option<usize>,
    pub(crate) model_count: Option<u64>,
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
        let mut idx = fxhash::hash(self);
        let node_type = match self.sdd_type.clone() {
            SddType::True => NodeType::Box("True".to_string()),
            SddType::False => NodeType::Box("False".to_string()),
            SddType::Literal(literal) => NodeType::Box(format!("{literal}")),
            SddType::Decision(node) => {
                idx = fxhash::hash(&node);
                for elem in node.elements.iter() {
                    elem.draw(writer, manager);
                    writer.add_edge(Edge::Simple(idx, fxhash::hash(&elem)));
                }
                NodeType::Circle(self.vtree_idx)
            }
        };

        writer.add_node(idx, node_type);
    }
}

impl Sdd {
    #[must_use]
    pub(crate) fn new(sdd_type: SddType, vtree_idx: u16, negation: Option<usize>) -> Sdd {
        let model_count = match sdd_type {
            SddType::False => Some(0),
            SddType::True | SddType::Literal(..) => Some(1),
            _ => None,
        };

        Sdd {
            sdd_type,
            vtree_idx,
            negation,
            model_count,
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
    fn is_trimmed(&self, manager: &SddManager) -> bool {
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

            primes.insert(prime.clone().negate(manager));
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
    fn is_compressed(&self, manager: &SddManager) -> bool {
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

    /// Trim decision node by replacing decompositions {(true, alpha)}
    /// and {(alpha, true), (!alpha, false)} with alpha. Returns a Boolean
    /// denoting whether the decision node had to be trimmed.
    fn trim(&self, manager: &SddManager) -> Option<Sdd> {
        let elements: Vec<&Element> = self.elements.iter().collect();
        if self.elements.len() == 1 {
            let el = elements.get(0).unwrap();
            if el.prime == Sdd::new_true().id() {
                match manager.get_node(el.sub) {
                    Some(sdd) => return Some(sdd),
                    None => panic!("el.sub must be present in unique_table"),
                }
            }
        }

        if self.elements.len() == 2 {
            let el_1 = elements.get(0).unwrap();
            let el_2 = elements.get(1).unwrap();

            let el_1_prime;
            let el_2_prime;
            if el_1.sub == Sdd::new_true().id() && el_2.sub == Sdd::new_false().id() {
                // Check for {(_, true), (_, false)}.
                el_1_prime = manager.get_node(el_1.prime).unwrap();
                el_2_prime = manager.get_node(el_2.prime).unwrap();
            } else if el_2.sub == Sdd::new_true().id() && el_1.sub == Sdd::new_false().id() {
                // Check for {(_, false), (_, true)}.
                el_1_prime = manager.get_node(el_2.prime).unwrap();
                el_2_prime = manager.get_node(el_1.prime).unwrap();
            } else {
                return None;
            }

            if el_1_prime.eq_negated(&el_2_prime, manager) {
                return Some(el_1_prime);
            }
        }

        None
    }

    /// Compress decision node by repeatedly replacing elements
    /// `(p, s)` and `(q, s)` with `(p || q, s)`.
    fn compress(&self, manager: &SddManager) -> Decision {
        let mut elements: Vec<_> = self.elements.iter().cloned().collect();
        let mut last_el_idx = self.elements.len() - 1;
        let mut i = 0;

        while i < last_el_idx {
            let mut j = i + 1;

            let mut fst = *elements.get(i).unwrap();
            while j <= last_el_idx {
                let snd = elements.get(j).unwrap();
                // TODO: Does this equality actually work? Can we just compare ids?
                if fst.sub != snd.sub {
                    j += 1;
                    continue;
                }

                // The subs are equal, we can compress the elements together.
                let fst_prime = manager.get_node(fst.prime).unwrap();
                let snd_prime = manager.get_node(snd.prime).unwrap();
                let new_prime = manager.disjoin(&fst_prime, &snd_prime);

                fst = Element {
                    prime: new_prime.id(),
                    sub: fst.sub,
                };

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
}

#[cfg(test)]
mod test {
    use super::{Decision, Element, Sdd, SddType};
    use crate::btreeset;
    use crate::literal::{Literal, Polarity};
    use crate::manager::SddManager;
    use crate::options::SddOptions;

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

        let a = create_literal(Literal::new(Polarity::Positive, "A"));
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
        assert_eq!(node, create_literal(Literal::new(Polarity::Positive, "A")));
    }

    #[test]
    fn not_trimmed_complex() {
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A"));
        let element_1 = Element {
            prime: (pos_a.id()),
            sub: (Sdd::new_true().id()),
        };

        let neg_a = create_literal(Literal::new(Polarity::Negative, "A"));
        let element_2 = Element {
            prime: (neg_a.id()),
            sub: (Sdd::new_false().id()),
        };

        // // Decomposition `{(A, true), (!A, false)}`.
        let decision = Decision {
            elements: btreeset!(element_1, element_2),
        };
        let sdd = Sdd {
            sdd_type: SddType::Decision(decision),
            vtree_idx: 0, // TODO: Fix vtree index
            negation: None,
            model_count: None,
        };

        let decisions = &vec![sdd.clone(), neg_a, pos_a];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager
            .get_node(sdd.id())
            .expect("node is not present in the unique table");
        assert!(!node.is_trimmed(&manager));

        let node = node.canonicalize(&manager);
        assert!(node.is_trimmed(&manager));
        assert_eq!(node, create_literal(Literal::new(Polarity::Positive, "A")));
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B"));
        let element_1_1 = Element {
            prime: Sdd::new_true().id(),
            sub: neg_b.id(),
        };

        // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
        let decision_1 = Decision {
            elements: btreeset!(element_1_1),
        };

        let sdd_1 = Sdd {
            sdd_type: SddType::Decision(decision_1),
            vtree_idx: 0, // TODO: Fix vtree index
            negation: None,
            model_count: None,
        };

        let pos_a = create_literal(Literal::new(Polarity::Positive, "A"));
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
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A"));
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
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B"));
        let element_1_1 = Element {
            prime: (neg_b.id()),
            sub: (Sdd::new_true().id()),
        };

        // Decomposition `{(!B, true)}`.
        let decision_1 = Decision {
            elements: btreeset!(element_1_1),
        };
        let sdd_1 = Sdd::new(SddType::Decision(decision_1), 0, None);

        let pos_a = create_literal(Literal::new(Polarity::Positive, "A"));
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
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A"));
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B"));
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
        let pos_a = create_literal(Literal::new(Polarity::Positive, "A"));
        let neg_b = create_literal(Literal::new(Polarity::Negative, "B"));
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
}
