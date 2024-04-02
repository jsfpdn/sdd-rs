#[allow(clippy::module_inception)]
mod sdd_test {
    use std::collections::HashMap;

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
        // TODO: Remove the hardcoded indices once the hashing scheme is implemented.
        let element = Element {
            prime: &Sdd::True,
            sub: &Sdd::False,
        };
        let decision = Decision {
            elements: btreeset!(&element),
        };

        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(true, false)}`.
                (0_u64, Sdd::DecisionRegular(&decision)),
            ]),
        );

        // Decomposition {(True, False)} is not trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_simple_2() {
        let element = Element {
            prime: &Sdd::True,
            sub: &boxed_literal(Polarity::Positive, "A"),
        };
        let decision = Decision {
            elements: btreeset!(&element),
        };

        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(true, A)}`.
                (0_u64, Sdd::DecisionRegular(&decision)),
            ]),
        );

        // Decomposition {(A, true)} is not trimmed.
        let node = manager.get_node(&0_u64).unwrap();
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
        let decision = Decision {
            elements: btreeset!(&element_1, &element_2),
        };

        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(A, true), (!A, false)}`.
                (0_u64, Sdd::DecisionRegular(&decision)),
            ]),
        );

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(!node.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let element_1_1 = Element {
            prime: &Sdd::True,
            sub: &boxed_literal(Polarity::Negative, "B"),
        };
        let decision_1 = &Decision {
            elements: btreeset!(&element_1_1),
        };
        let element_2_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };
        let element_2_2 = Element {
            prime: &Sdd::DecisionRegular(decision_1),
            sub: &Sdd::False,
        };
        let decision_2 = Decision {
            elements: btreeset!(&element_2_1, &element_2_2),
        };

        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
                (0_u64, Sdd::DecisionRegular(&decision_1)),
                // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
                (1_u64, Sdd::DecisionRegular(&decision_2)),
            ]),
        );

        let node = manager.get_node(&1_u64).unwrap();
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
        let decision = Decision {
            elements: btreeset!(&element_1, &element_2),
        };

        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(A, true), (B, false)}`.
                (0_u64, Sdd::DecisionRegular(&decision)),
            ]),
        );

        // Decomposition {(A, true), (B, false)} is trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(node.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        let element_1_1 = Element {
            prime: &boxed_literal(Polarity::Negative, "B"),
            sub: &Sdd::True,
        };
        let decision_1 = &Decision {
            elements: btreeset!(&element_1_1),
        };

        let element_2_1 = Element {
            prime: &boxed_literal(Polarity::Positive, "A"),
            sub: &Sdd::True,
        };
        let element_2_2 = Element {
            prime: &Sdd::DecisionRegular(decision_1),
            sub: &Sdd::False,
        };
        let decision_2 = Decision {
            elements: btreeset!(&element_2_1, &element_2_2),
        };

        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(!B, true)}`.
                (0_u64, Sdd::DecisionRegular(&decision_1)),
                // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
                (1_u64, Sdd::DecisionRegular(&decision_2)),
            ]),
        );

        let node = manager.get_node(&1_u64).unwrap();
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
