//! Example minimization of compiled knowledge via vtree fragments.

use sddrs::{
    literal::literal::Polarity,
    manager::{
        options::{self, FragmentHeuristic, GarbageCollection, MinimizationCutoff, VTreeStrategy},
        SddManager,
    },
};

fn main() {
    let opts = options::SddOptions::builder()
        .vtree_strategy(VTreeStrategy::LeftLinear)
        .garbage_collection(GarbageCollection::Automatic)
        .variables(&["A".to_string(), "B".to_string(), "C".to_string()])
        .build();
    let manager = SddManager::new(&opts);

    let a = manager.literal("A", Polarity::Positive).unwrap();
    let b = manager.literal("B", Polarity::Positive).unwrap();
    let c = manager.literal("C", Polarity::Positive).unwrap();

    let conjunction = manager.conjoin(&a, &manager.conjoin(&b, &c));
    let size_before = conjunction.size();
    println!("size for right-linear: {}", size_before);

    manager
        .minimize(
            MinimizationCutoff::BreakAfterFirstImprovement,
            &FragmentHeuristic::Root,
            &conjunction,
        )
        .unwrap();

    let size_after = conjunction.size();
    println!("size after minimizing via fragments: {}", size_after);

    // Ideally, this should hold:
    assert!(size_after <= size_before);
}
