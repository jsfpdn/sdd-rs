//! Manager responsible for manipulating and querying SDDs as well as maintaining
//! the state of the compilation.
mod manager;

pub mod dimacs;
pub mod model;
pub mod options;

pub use crate::manager::manager::*;
