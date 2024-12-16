//! Example of simple knowledge compilation.
use sddrs::{
    literal::literal::Polarity,
    manager::{
        options::{self, GarbageCollection, VTreeStrategy},
        SddManager,
    },
};

fn main() {
    let opts = options::SddOptions::builder()
        .vtree_strategy(VTreeStrategy::RightLinear)
        .garbage_collection(GarbageCollection::Automatic)
        .variables(&["A".to_string(), "B".to_string(), "C".to_string()])
        .build();

    let manager = SddManager::new(&opts);

    let a = manager.literal("A", Polarity::Positive).unwrap();
    let n_b = manager.literal("B", Polarity::Negative).unwrap();
    let c = manager.literal("C", Polarity::Positive).unwrap();

    // A && !B
    let fst = manager.conjoin(&a, &n_b);
    assert_eq!(manager.model_count(&fst), 2);
    println!("A && !B:\n{}\n", manager.model_enumeration(&fst));

    // C => (A && !B)
    let snd = manager.imply(&c, &fst);
    assert_eq!(manager.model_count(&snd), 5);
    println!("C => (A && !B):\n{}\n", manager.model_enumeration(&snd));

    // !(C => (A && !B))
    let n_snd = manager.negate(&snd);
    assert_eq!(manager.model_count(&n_snd), 3);
    println!("!(C => A && !B):\n{}\n", manager.model_enumeration(&n_snd));

    // (C => (A && !B)) <=> !(C => (A && !B)) == False
    let ff = manager.equiv(&snd, &n_snd);
    assert_eq!(manager.model_count(&ff), 0);
    assert!(ff.is_false());
    println!("False:\n{}\n", manager.model_enumeration(&ff));
}
