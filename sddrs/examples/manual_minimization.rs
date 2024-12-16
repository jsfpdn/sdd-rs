//! Example of manual minimization of compiled knowledge.
use sddrs::{
    literal::literal::Polarity,
    manager::{
        options::{self, GarbageCollection, VTreeStrategy},
        SddManager,
    },
};

fn main() {
    let opts = options::SddOptions::builder()
        //    x
        //   / \
        //  A   y
        //     / \
        //    B   C
        .vtree_strategy(VTreeStrategy::RightLinear)
        .garbage_collection(GarbageCollection::Automatic)
        .variables(&["A".to_string(), "B".to_string(), "C".to_string()])
        .build();
    let manager = SddManager::new(&opts);

    let a = manager.literal("A", Polarity::Positive).unwrap();
    let b = manager.literal("B", Polarity::Positive).unwrap();
    let c = manager.literal("C", Polarity::Positive).unwrap();

    // A && B && C
    let conjunction = manager.conjoin(&a, &manager.conjoin(&b, &c));
    println!("size for right-linear: {}", conjunction.size());

    // Rotate 'x' to obtain this vtree:
    //     x
    //    / \
    //   y   C
    //  / \
    // A   B
    manager
        .rotate_left(&manager.root().right_child().unwrap())
        .unwrap();
    println!(
        "size after rotating 'x' to the left: {}",
        conjunction.size()
    );

    // Swap children of 'y' to obtain this vtree:
    //     x
    //    / \
    //   y   C
    //  / \
    // B   A
    manager.swap(&manager.root().left_child().unwrap()).unwrap();
    println!(
        "size after swapping children of 'y': {}",
        conjunction.size()
    );
}
