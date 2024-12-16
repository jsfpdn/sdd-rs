use sddrs::manager::{
    options::{self, GarbageCollection, VTreeStrategy},
    SddManager,
};

fn main() {
    let opts = options::SddOptions::builder()
        .vtree_strategy(VTreeStrategy::LeftLinear)
        .garbage_collection(GarbageCollection::Automatic)
        .variables(&[
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ])
        .build();
    let manager = SddManager::new(&opts);

    let dimacs = "c
p cnf 4 3
1 3 -4 0
4 0
2 -3 0
";
    let sdd = manager.from_dimacs(&mut dimacs.as_bytes()).unwrap();

    println!("Compiled SDD in DOT Graphviz format:");
    manager.draw_sdd(&mut std::io::stdout(), &sdd).unwrap();

    println!("\n---\nVtree in DOT Graphviz format:");
    manager.draw_vtree(&mut std::io::stdout()).unwrap();
    println!();
}
