use std::collections::{BTreeSet, HashSet};
use std::hash::Hash;

use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::Literal,
    manager::SddManager,
};

#[derive(PartialEq, Eq, Clone, Hash)]
pub struct Node<'a> {
    decision: &'a Decision<'a>,

    parents: u64,
    refs: u64,
    // TODO: Do we want field `parents: BTreeSet<u64>`? What would this point to? Since only the
    // decision nodes will be stored in the unique_table, then it would have to point to decision
    // node, not to the particular element pointing to it (since it is not hashed and stored
    // directly in the unique_table).
}

impl<'a> Node<'a> {
    #[must_use]
    pub fn new(decision: &'a Decision) -> Node<'a> {
        Node {
            decision,
            parents: 0,
            refs: 0,
        }
    }
}

// Element node (a paired box) is a conjunction of prime and sub.
#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub struct Element<'a> {
    // TODO: Remove `pub` visibility modifiers once done with testing.
    pub prime: &'a Sdd<'a>,
    pub sub: &'a Sdd<'a>,
}

impl<'a> Element<'a> {
    fn is_trimmed(&self, manager: &SddManager) -> bool {
        self.prime.is_trimmed(manager) && self.sub.is_trimmed(manager)
    }

    fn is_compressed(&self, manager: &SddManager) -> bool {
        self.prime.is_compressed(manager) && self.sub.is_compressed(manager)
    }
}

impl<'a> Dot for Element<'a> {
    fn draw(&self, writer: &mut DotWriter) {
        let idx = fxhash::hash(self);

        writer.add_node(
            idx,
            NodeType::Record(self.prime.dot_repr(), self.sub.dot_repr()),
        );

        if let Sdd::DecisionRegular(node) | Sdd::DecisionComplement(node) = self.prime {
            writer.add_edge(Edge::Prime(idx, fxhash::hash(node)));
        }
        if let Sdd::DecisionRegular(node) | Sdd::DecisionComplement(node) = self.sub {
            writer.add_edge(Edge::Sub(idx, fxhash::hash(node)));
        };
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub enum Sdd<'a> {
    True,
    False,
    Literal(Literal),
    DecisionRegular(&'a Decision<'a>),
    DecisionComplement(&'a Decision<'a>),
}

impl<'a> Dot for Sdd<'a> {
    fn draw(&self, writer: &mut DotWriter) {
        let mut idx = fxhash::hash(self);
        let node_type = match self {
            Sdd::True => NodeType::Box("True".to_owned()),
            Sdd::False => NodeType::Box("False".to_owned()),
            Sdd::Literal(literal) => NodeType::Box(format!("{literal}")),
            Sdd::DecisionComplement(node) | Sdd::DecisionRegular(node) => {
                idx = fxhash::hash(node);
                for elem in &node.elements {
                    elem.draw(writer);
                    writer.add_edge(Edge::Simple(idx, fxhash::hash(elem)));
                }
                // TODO: Add proper vtree index to the NodeType::Circle once implemented.
                NodeType::Circle(42)
            }
        };

        writer.add_node(idx, node_type);
    }
}

impl<'a> Sdd<'a> {
    #[must_use]
    pub fn id(&self) -> usize {
        match self {
            Sdd::DecisionComplement(decision) | Sdd::DecisionRegular(decision) => {
                fxhash::hash(decision)
            }
            _ => fxhash::hash(self),
        }
    }

    fn is_true(&self) -> bool {
        matches!(self, Sdd::True)
    }

    fn is_false(&self) -> bool {
        matches!(self, Sdd::False)
    }

    fn is_constant(&self) -> bool {
        self.is_true() || self.is_false()
    }

    fn negate(&self) -> Sdd {
        match self {
            Sdd::True => Sdd::False,
            Sdd::False => Sdd::True,
            Sdd::Literal(literal) => Sdd::Literal(literal.negate()),
            Sdd::DecisionRegular(decision) => Sdd::DecisionComplement(decision.to_owned()),
            Sdd::DecisionComplement(decision) => Sdd::DecisionRegular(decision.to_owned()),
        }
    }

    fn eq_negated(&self, other: &Sdd) -> bool {
        match (self, other) {
            (Sdd::True, Sdd::False) | (Sdd::False, Sdd::True) => true,
            (Sdd::Literal(fst), Sdd::Literal(snd)) => fst.eq_negated(snd),
            // TODO: Is this correct? This smells fishy.
            (Sdd::DecisionRegular(fst), Sdd::DecisionComplement(snd))
            | (Sdd::DecisionComplement(fst), Sdd::DecisionRegular(snd)) => fst == snd,
            (_, _) => false,
        }
    }

    fn is_trimmed(&self, manager: &SddManager) -> bool {
        match self {
            Sdd::True | Sdd::False | Sdd::Literal(_) => true,
            Sdd::DecisionRegular(decision) | Sdd::DecisionComplement(decision) => {
                decision.is_trimmed(manager)
            }
        }
    }

    fn is_compressed(&self, manager: &SddManager) -> bool {
        match self {
            Sdd::True | Sdd::False | Sdd::Literal(_) => true,
            Sdd::DecisionRegular(decision) | Sdd::DecisionComplement(decision) => {
                decision.is_compressed(manager)
            }
        }
    }

    /// # Panics
    /// Function panics if `self` or `other` are decision nodes containing indexes
    /// to SDD nodes not existing in the manager.
    #[must_use]
    pub fn and(&'a self, other: &'a Sdd, _manager: &SddManager) -> &'a Sdd {
        // Handle simple cases first.
        if other.is_false() {
            return &Sdd::False;
        }

        if other.is_true() {
            return self;
        }

        if self.eq(other) {
            return self;
        }

        if self.eq_negated(other) {
            return &Sdd::False;
        }

        let (_sdd1, _sdd2) = match (self, other) {
            (Sdd::True, _) => return other,
            (_, Sdd::True) => return self,
            (Sdd::False, _) | (_, Sdd::False) => return &Sdd::False,
            (
                Sdd::DecisionRegular(fst) | Sdd::DecisionComplement(fst),
                Sdd::DecisionRegular(snd) | Sdd::DecisionComplement(snd),
            ) => (fst, snd),
            (Sdd::Literal(_fst), Sdd::Literal(_snd)) => unimplemented!(""),
            _ => unimplemented!(""),
        };

        unimplemented!("TODO");
    }

    #[must_use]
    pub fn or(&self, _other: &Sdd, _manager: &SddManager) -> Sdd {
        // Compute by De Morgan's laws?
        unimplemented!("TODO")
    }

    fn dot_repr(&self) -> String {
        match self {
            Sdd::True => String::from("⊤"),
            Sdd::False => String::from("⊥"),
            Sdd::Literal(literal) => format!("{literal}"),
            _ => String::new(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub struct Decision<'a> {
    // TODO: Remove `pub` visibility modifiers once done with testing.
    pub elements: BTreeSet<&'a Element<'a>>,
}

impl<'a> Decision<'a> {
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
            if primes.contains(element.prime) {
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
        let mut subs: HashSet<&'a Sdd> = HashSet::new();
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

#[cfg(test)]
mod test {
    use crate::{
        btreeset,
        literal::{Literal, Polarity, VarLabel},
        options::SddOptions,
        sdd::{Decision, Element, Sdd, SddManager},
    };

    fn boxed_literal<'a>(polarity: Polarity, var_label: &str) -> Sdd<'a> {
        Sdd::Literal(Literal::new(polarity, VarLabel::new(var_label)))
    }

    #[test]
    fn not_trimmed_simple() {
        let element = Element {
            prime: &Sdd::True,
            sub: &Sdd::False,
        };

        // Decomposition `{(true, false)}`.
        let decision = &Decision {
            elements: btreeset!(&element),
        };
        let sdd = &Sdd::DecisionRegular(decision);

        let decisions = &vec![sdd];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition {(True, False)} is not trimmed.
        let node = manager.get_node(sdd.id());
        assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_simple_2() {
        let element = Element {
            prime: &Sdd::True,
            sub: &boxed_literal(Polarity::Positive, "A"),
        };

        // Decomposition `{(true, A)}`.
        let decision = &Decision {
            elements: btreeset!(&element),
        };
        let sdd = &Sdd::DecisionRegular(decision);

        let decisions = &vec![sdd];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition {(A, true)} is not trimmed.
        let node = manager.get_node(sdd.id());
        assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_complex() {
        let element_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };
        let element_2 = Element {
            prime: &boxed_literal(Polarity::Negative, "A"),
            sub: &Sdd::False,
        };

        // Decomposition `{(A, true), (!A, false)}`.
        let decision = &Decision {
            elements: btreeset!(&element_1, &element_2),
        };
        let sdd = &Sdd::DecisionRegular(decision);

        let decisions = &vec![sdd];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager.get_node(sdd.id());
        assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let element_1_1 = Element {
            prime: &Sdd::True,
            sub: &boxed_literal(Polarity::Negative, "B"),
        };

        // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
        let decision_1 = &Decision {
            elements: btreeset!(&element_1_1),
        };

        let sdd_1 = &Sdd::DecisionRegular(decision_1);

        let element_2_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };

        let element_2_2 = Element {
            prime: &Sdd::DecisionRegular(decision_1),
            sub: &Sdd::False,
        };

        // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
        let decision_2 = &Decision {
            elements: btreeset!(&element_2_1, &element_2_2),
        };

        let sdd_2 = &Sdd::DecisionRegular(decision_2);

        let decisions = &vec![sdd_1, sdd_2];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        let node = manager.get_node(sdd_2.id());
        assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_complex() {
        let element_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };
        let element_2 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::False,
        };

        // Decomposition `{(A, true), (B, false)}`.
        let decision = &Decision {
            elements: btreeset!(&element_1, &element_2),
        };
        let sdd = &Sdd::DecisionRegular(decision);

        let decisions = &vec![sdd];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        // Decomposition {(A, true), (B, false)} is trimmed.
        let node = manager.get_node(sdd.id());
        assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        let element_1_1 = Element {
            prime: &boxed_literal(Polarity::Negative, "B"),
            sub: &Sdd::True,
        };

        // Decomposition `{(!B, true)}`.
        let decision_1 = &Decision {
            elements: btreeset!(&element_1_1),
        };
        let sdd_1 = &Sdd::DecisionRegular(decision_1);

        let element_2_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };
        let element_2_2 = Element {
            prime: sdd_1,
            sub: &Sdd::False,
        };

        // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
        let decision_2 = &Decision {
            elements: btreeset!(&element_2_1, &element_2_2),
        };
        let sdd_2 = &Sdd::DecisionRegular(decision_2);

        let decisions = &vec![sdd_1, sdd_2];
        let manager = SddManager::new_with_nodes(SddOptions::new(), decisions);

        let node = manager.get_node(sdd_2.id());
        assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn not_compressed() {
        // TODO: Implement me!
    }

    #[test]
    fn compressed() {
        // TODO: Implement me!
    }

    #[test]
    fn sdd_hashing() {
        let element_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };

        let element_2 = Element {
            prime: &boxed_literal(Polarity::Negative, "A"),
            sub: &Sdd::True,
        };

        let decision_1 = &Decision {
            elements: btreeset!(&element_1),
        };

        let decision_2 = &Decision {
            elements: btreeset!(&element_2),
        };

        assert!(
            &Sdd::DecisionRegular(decision_1).id() == &Sdd::DecisionComplement(decision_1).id()
        );

        assert!(&Sdd::DecisionRegular(decision_1).id() != &Sdd::DecisionRegular(decision_2).id());
    }
}
