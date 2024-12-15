# sddrs: Bottom-Up Sentential Decision Diagram Compiler

**Incrementally build, manipualate, and optimize
[Sentential Decision Diagrams (SDD)](https://en.wikipedia.org/wiki/Sentential_decision_diagram):
a succinct representation of Boolean functions.**

## Features

The compiler currently supports:

* incremental compilation of Boolean functions (knowledge bases) to *compressed* and *trimmed* SDDs,
* efficient querying of model count, model enumeration, and equivalence of SDDs,
* dynamic minimization of SDDs via *vtree fragments*,
* garbage collection of dead nodes,
* SDD compilation from CNF in
  [DIMACS](https://www21.in.tum.de/~lammich/2015_SS_Seminar_SAT/resources/dimacs-cnf.pdf) format.

## Usage

The following snippet compiles the function $(A \land B) \lor C$ to an SDD,
computes number of its models, enumerates and prints them to the stdout,
and renders the compiled SDD and its vtree to the DOT format.

```rust
use sddrs::manager::{options, GCStatistics, SddManager};
use sddrs::literal::literal::Polarity;
use bon::arr;

fn main() {
    let options = options::SddOptions::builder()
        // Create right-linear vtree.
        .vtree_strategy(options::VTreeStragey::RightLinear)
        // Initialize the manager with variables A, B, and C.
        .variables(["A".to_string(), "B".to_string(), "C"])
        .build();
    let manager = SddManager::new(options);

    // Retrieve SDDs for literals A, B, and C.
    let a = manager.literal("A", Polarity::Positive).unwrap();
    let b = manager.literal("B", Polarity::Positive).unwrap();
    let c = manager.literal("C", Polarity::Positive).unwrap();

    // Compute "A ∧ B"
    let a_and_b = manager.conjoin(&a, &b);
    // Compute "(A ∧ B) ∨ C"
    let a_and_b_or_c = manager.disjoin(&a_and_b, &c);

    let model_count = manager.model_count(&a_and_b_or_c);
    let models = manager.model_enumeration(&a_and_b_or_c);

    println!("'(A ∧ B) ∨ C' has {model_count} models.");
    println!("They are:\n{models}");

    let sdd_path = "my_formula.dot"
    let f = File::create(sdd_path).unwrap();
    let mut b = BufWriter::new(f);
    manager
        .draw_sdd(&mut b as &mut dyn std::io::Write, &sdd)
        .unwrap();

    let vtree_path = "my_vtree.dot"
    let f = File::create(vtree_path).unwrap();
    let mut b = BufWriter::new(f);
    manager
        .draw_vtree(&mut b as &mut dyn std::io::Write)
        .unwrap();

    println!("Rendered SDD to '{sdd_path}' and vtree to '{vtree_path}'");
}
```

## :page_with_curl: Related Links

* [SDD: A New Canonical Representation of Propositional Knowledge Bases - Adnad Darwiche](http://reasoning.cs.ucla.edu/fetch.php?id=121&type=pdf):
  paper introducing SDDs
* [Dynamic Minimization of Sentential Decision Diagrams - Arthur Choi and Adnan Darwiche](http://reasoning.cs.ucla.edu/fetch.php?id=128&type=pdf):
  paper describing dynamic minimization of SDDs
* [SDD: A New Canonical Representation of Propositional Knowledge Bases – Adnan Darwiche (YouTube tutorial)](https://www.youtube.com/watch?v=_5Estmve91o)
* [Bottom-Up Knowledge Compilers – Adnan Darwiche (YouTube tutorial)](https://www.youtube.com/watch?v=8yZapazT9Ls)
* [The SDD Package homepage](http://reasoning.cs.ucla.edu/sdd/): homepage of the original C SDD compiler
* [RSDD](https://github.com/neuppl/rsdd): alternative implementation of SDD in Rust
