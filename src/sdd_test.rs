mod tests {
    use std::collections::HashMap;

    use crate::{
        literal::{Literal, VarLabel},
        options::SddOptions,
        sdd::{Node, Sdd, SddAnd, SddManager, SddOr},
    };

    #[test]
    fn not_trimmed_simple() {
        // TODO: Remove the hardcoded indices once the hashing scheme is implemented.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(2), 0)),
                // Constant `false`.
                (1_u64, Node::new(Sdd::False, Some(2), 1)),
                // Element `(true, false).`
                (
                    2_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 1 }), Some(42), 2),
                ),
                // Decomposition `{(true, false)}`.
                (
                    3_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![2] }), None, 3),
                ),
            ]),
        );

        // Decomposition {(True, False)} is not trimmed.
        let node = manager.get_node(&3_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_simple_2() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Literal `A`.
                (
                    1_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        1,
                    ),
                ),
                // Element `(true, A)`.
                (
                    2_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 1 }), Some(42), 2),
                ),
                // Decomposition `{(true, A)}`.
                (
                    3_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![2] }), None, 3),
                ),
            ]),
        );

        // Decomposition {(A, true)} is not trimmed.
        let node = manager.get_node(&3_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_complex() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(4), 0)),
                // Constant `false`.
                (1_u64, Node::new(Sdd::False, Some(5), 1)),
                // Literal `A`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(4),
                        2,
                    ),
                ),
                // Literal `!A`.
                (
                    3_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(0))),
                        Some(5),
                        3,
                    ),
                ),
                // Element `(A, True)`.
                (
                    4_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 2, sub: 0 }), Some(42), 4),
                ),
                // Element `(!A, False)`.
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 3, sub: 1 }), Some(42), 5),
                ),
                // Decomposition `{(A, true), (!A, false)}`.
                (
                    6_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![4, 5],
                        }),
                        Some(42),
                        6,
                    ),
                ),
            ]),
        );

        // Decomposition `{(A, true), (!A, false)}` is not trimmed.
        let node = manager.get_node(&6_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn not_trimmed_recursive() {
        // Check that decomposition is recursivelly checked.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Literal `A`.
                (
                    1_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        1,
                    ),
                ),
                // Literal `!B`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(1))),
                        Some(42),
                        2,
                    ),
                ),
                (
                    3_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 2 }), Some(42), 3),
                ),
                // Decomposition `{(true, !B)}`. This is where the SDD stops being trimmed.
                (
                    4_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![3] }), Some(42), 4),
                ),
                // Element `(A, true)`.
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 1, sub: 0 }), Some(42), 5),
                ),
                // Constant `false`.
                (6_u64, Node::new(Sdd::False, Some(42), 6)),
                // Element `(ptr, false)` where ptr is the decomposition `{(true, !B)}`.
                (
                    7_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 4, sub: 6 }), Some(42), 7),
                ),
                // Decomposition `{(A, true), (ptr, false)}` where ptr is the decomposition `{(true, !B)}`.
                (
                    8_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![4, 7],
                        }),
                        Some(42),
                        8,
                    ),
                ),
            ]),
        );

        let node = manager.get_node(&7_u64).unwrap();
        assert!(!node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_simple() {
        // TODO: Remove the hardcoded indices once the hashing scheme is implemented.
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                (0_u64, Node::new(Sdd::False, Some(42), 0)),
                (
                    1_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 0, sub: 0 }), None, 1),
                ),
            ]),
        );

        // Decomposition {(false, false)} is trimmed.
        let node = manager.get_node(&1_u64).unwrap();
        assert!(node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_complex() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `True`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Literal `A`.
                (
                    1_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        1,
                    ),
                ),
                // Literal `!B`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(1))),
                        Some(42),
                        2,
                    ),
                ),
                // Element `(A, true)`.
                (
                    3_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 1, sub: 0 }), Some(42), 3),
                ),
                // Constant `false`.
                (4_u64, Node::new(Sdd::False, Some(42), 4)),
                // Element `(!B, false)`.
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 2, sub: 4 }), Some(42), 5),
                ),
                // Decomposition `{(A, true), (B, false)}`.
                (
                    6_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![3, 5],
                        }),
                        None,
                        6,
                    ),
                ),
            ]),
        );

        // Decomposition {(A, true), (B, false)} is trimmed.
        let node = manager.get_node(&6_u64).unwrap();
        assert!(node.sdd.is_trimmed(&manager));
    }

    #[test]
    fn trimmed_recursive() {
        let manager = SddManager::new_with_nodes(
            SddOptions::new(),
            HashMap::from([
                // Constant `true`.
                (0_u64, Node::new(Sdd::True, Some(42), 0)),
                // Constant `false`.
                (1_u64, Node::new(Sdd::False, Some(42), 1)),
                // Literal `A`.
                (
                    2_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(true, VarLabel::new(0))),
                        Some(42),
                        2,
                    ),
                ),
                // Literal `!B`.
                (
                    3_u64,
                    Node::new(
                        Sdd::Literal(Literal::new(false, VarLabel::new(1))),
                        Some(42),
                        3,
                    ),
                ),
                // Element `(!B, true)`
                (
                    4_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 3, sub: 0 }), Some(42), 4),
                ),
                // Element `(A, true)`
                (
                    5_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 2, sub: 0 }), Some(42), 5),
                ),
                // Decomposition `{(!B, true)}`.
                (
                    6_u64,
                    Node::new(Sdd::Decision(SddOr { elements: vec![4] }), Some(42), 6),
                ),
                // Element `(ptr, false)` where ptr is `{(!B, true)}`.
                (
                    7_u64,
                    Node::new(Sdd::Element(SddAnd { prime: 6, sub: 1 }), Some(42), 7),
                ),
                // Decomposition `{(A, true), (ptr, false)}`, where ptr is `{(!B, true)}`.
                (
                    8_u64,
                    Node::new(
                        Sdd::Decision(SddOr {
                            elements: vec![5, 7],
                        }),
                        Some(42),
                        8,
                    ),
                ),
            ]),
        );

        let node = manager.get_node(&8_u64).unwrap();
        assert!(node.sdd.is_trimmed(&manager));
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
