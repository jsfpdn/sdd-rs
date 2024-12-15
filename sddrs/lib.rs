//! # Bottom-up compiler for Sentential Decision Diagrams.
//!
//! Incrementally build, manipualate, and optimize
//! [Sentential Decision Diagrams (SDD)](https://en.wikipedia.org/wiki/Sentential_decision_diagram):
//! a succinct representation of Boolean functions.
//!
//! The compiler currently supports:
//! * incremental compilation of Boolean functions (knowledge bases) to *compressed* and *trimmed* SDDs,
//! * efficient querying of model count, model enumeration, and equivalence of SDDs,
//! * dynamic minimization of SDDs via *vtree fragments*,
//! * garbage collection of dead nodes,
//! * SDD compilation from CNF in [DIMACS](https://www21.in.tum.de/~lammich/2015_SS_Seminar_SAT/resources/dimacs-cnf.pdf) format.
//!
//! The following snippet compiles the function `(A ∧ B) ∨ C` to SDD,
//! computes number of its models, enumerates and prints them to the stdout,
//! and renders the compiled SDD and its vtree to the DOT format.
//!
//! ```rust
//! use sddrs::manager::{options, GCStatistics, SddManager};
//! use sddrs::literal::literal::Polarity;
//! use bon::arr;
//!
//! let options = options::SddOptions::builder()
//!     // Create right-linear vtree.
//!     .vtree_strategy(options::VTreeStragey::RightLinear)
//!     // Initialize the manager with variables A, B, and C.
//!     .variables(["A".to_string(), "B".to_string(), "C".to_string()])
//!     .build();
//! let manager = SddManager::new(options);
//!
//! // Retrieve SDDs for literals A, B, and C.
//! let a = manager.literal("A", Polarity::Positive).unwrap();
//! let b = manager.literal("B", Polarity::Positive).unwrap();
//! let c = manager.literal("C", Polarity::Positive).unwrap();
//!
//! // Compute "A ∧ B"
//! let a_and_b = manager.conjoin(&a, &b);
//! // Compute "(A ∧ B) ∨ C"
//! let a_and_b_or_c = manager.disjoin(&a_and_b, &c);
//!
//! let model_count = manager.model_count(&a_and_b_or_c);
//! let models = manager.model_enumeration(&a_and_b_or_c);
//!
//! println!("'(A ∧ B) ∨ C' has {model_count} models.");
//! println!("They are:\n{models}");
//!
//! let sdd_path = "my_formula.dot"
//! let f = File::create(sdd_path).unwrap();
//! let mut b = BufWriter::new(f);
//! manager
//!     .draw_sdd(&mut b as &mut dyn std::io::Write, &sdd)
//!      .unwrap();
//!
//! let vtree_path = "my_vtree.dot"
//! let f = File::create(vtree_path).unwrap();
//! let mut b = BufWriter::new(f);
//! manager
//!     .draw_vtree(&mut b as &mut dyn std::io::Write)
//!     .unwrap();
//!
//! println!("Rendered SDD to '{sdd_path}' and vtree to '{vtree_path}'");
//! ```
//!
//! ---
//!
//! Main methods to compile SDDs are:
//!
//! * [`crate::manager::SddManager::conjoin`] -- compute AND of two SDDs
//! * [`crate::manager::SddManager::disjoin`] -- compute OR of two SDDs
//! * [`crate::manager::SddManager::imply`] -- compute implication of two SDDs
//! * [`crate::manager::SddManager::equiv`] -- compute equivalence of two SDDs
//! * [`crate::manager::SddManager::negate`] -- compute negation of SDD
//!
//! Main methods to query SDDs are:
//!
//! * [`crate::manager::SddManager::model_count`] -- count the number of models of an SDD
//! * [`crate::manager::SddManager::model_enumeration`] -- enumerate models of an SDD
//! * [`crate::sdd::SddRef::size`] -- get size of the SDD
//!
//! SDDs can be also minimized after compilation by appropriately manipulating the vtree:
//!
//! * [`crate::manager::SddManager::swap`] -- swap children of a vtree and adjust SDDs
//! * [`crate::manager::SddManager::rotate_right`] -- rotate vtree node to the right and adjust SDDs
//! * [`crate::manager::SddManager::rotate_left`] -- rotate vtree node to the left and adjust SDDs
//!
//! These transformations do not guarantee that the SDD will decrease in size. In fact, it may grow.
//! For this purpose, dynamic minimization via [`crate::vtree::fragment::Fragment`] tries to find
//! the vtree that actually minimizes the SDD the most [`crate::manager::SddManager::minimize`].
//!
//! There are also additional helper functions:
//!
//! * [`crate::manager::SddManager::from_dimacs`] -- compile SDD based on a DIMACS CNF file
//! * [`crate::manager::SddManager::draw_sdd`] -- draw a particular SDD to a DOT Graphviz format
//! * [`crate::manager::SddManager::draw_all_sdds`] -- draw every SDDs to a DOT Graphviz format
//! * [`crate::manager::SddManager::draw_vtree`] -- draw vtree a DOT Graphviz format
//!
//!
//! Additional resources:
//!
//! * [SDD: A New Canonical Representation of Propositional Knowledge Bases - Adnad Darwiche](http://reasoning.cs.ucla.edu/fetch.php?id=121&type=pdf):
//!   paper introducing SDDs
//! * [Dynamic Minimization of Sentential Decision Diagrams - Arthur Choi and Adnan Darwiche](http://reasoning.cs.ucla.edu/fetch.php?id=128&type=pdf):
//!   paper describing dynamic minimization of SDDs
//! * [SDD: A New Canonical Representation of Propositional Knowledge Bases – Adnan Darwiche](https://www.youtube.com/watch?v=_5Estmve91o): YouTube tutorial

/// Variables, polarities, and literals.
pub mod literal;
pub mod manager;
pub mod sdd;
#[macro_use]
pub(crate) mod util;
pub(crate) mod dot_writer;
pub mod vtree;
