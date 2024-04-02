#[allow(clippy::module_inception)]
mod sdd_test {
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
}
