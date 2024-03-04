#[allow(clippy::module_inception)]
mod sdd_test {
    use std::collections::HashMap;

    use crate::{
        literal::{Literal, VarLabel},
        options::SddOptions,
        sdd::{Box, Decision, Element, Node, SddManager},
        util::btreeset,
    };

    fn boxed_literal(polarity: bool, var_label: u64) -> Box {
        Box::Literal(Literal::new(polarity, VarLabel::new(var_label)))
    }

    #[test]
    fn not_trimmed_simple() {
        // TODO: Remove the hardcoded indices once the hashing scheme is implemented.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(true, false)}`.
                (
                    0_u64,
                    Node::new(Decision {
                        elements: btreeset!(Element {
                            prime: Box::True,
                            sub: Box::False
                        }),
                    }),
                ),
            ]),
        );

        // Decomposition {(True, False)} is not trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(!node.decision.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_simple_2() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(true, A)}`.
                (
                    0_u64,
                    Node::new(Decision {
                        elements: btreeset!(Element {
                            prime: Box::True,
                            sub: boxed_literal(true, 0),
                        }),
                    }),
                ),
            ]),
        );

        // Decomposition {(A, true)} is not trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(!node.decision.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_complex() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(A, true), (!A, false)}`.
                (
                    0_u64,
                    Node::new(Decision {
                        elements: btreeset!(
                            Element {
                                prime: boxed_literal(true, 0),
                                sub: Box::True
                            },
                            Element {
                                prime: boxed_literal(false, 0),
                                sub: Box::False
                            }
                        ),
                    }),
                ),
            ]),
        );

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(!node.decision.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
                (
                    0_u64,
                    Node::new(Decision {
                        elements: btreeset!(Element {
                            prime: Box::True,
                            sub: boxed_literal(false, 1)
                        }),
                    }),
                ),
                // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
                (
                    1_u64,
                    Node::new(Decision {
                        elements: btreeset!(
                            Element {
                                prime: boxed_literal(true, 0),
                                sub: Box::True
                            },
                            Element {
                                prime: Box::DecisionRegular(0_u64),
                                sub: Box::False
                            }
                        ),
                    }),
                ),
            ]),
        );

        let node = manager.get_node(&1_u64).unwrap();
        assert!(!node.decision.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_complex() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(A, true), (B, false)}`.
                (
                    0_u64,
                    Node::new(Decision {
                        elements: btreeset!(
                            Element {
                                prime: boxed_literal(true, 0),
                                sub: Box::True
                            },
                            Element {
                                prime: boxed_literal(true, 0),
                                sub: Box::False
                            }
                        ),
                    }),
                ),
            ]),
        );

        // Decomposition {(A, true), (B, false)} is trimmed.
        let node = manager.get_node(&0_u64).unwrap();
        assert!(node.decision.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Decomposition `{(!B, true)}`.
                (
                    0_u64,
                    Node::new(Decision {
                        elements: btreeset!(Element {
                            prime: boxed_literal(false, 1),
                            sub: Box::True
                        }),
                    }),
                ),
                // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
                (
                    1_u64,
                    Node::new(Decision {
                        elements: btreeset!(
                            Element {
                                prime: boxed_literal(true, 0),
                                sub: Box::True
                            },
                            Element {
                                prime: Box::DecisionRegular(0_u64),
                                sub: Box::False
                            }
                        ),
                    }),
                ),
            ]),
        );

        let node = manager.get_node(&1_u64).unwrap();
        assert!(node.decision.is_trimmed(&manager));
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
