#![allow(clippy::module_inception)]

mod manager;

pub mod dimacs;
pub mod model;
pub mod options;

pub use crate::manager::manager::*;
