pub mod literal;
pub mod manager;
pub mod sdd;
#[macro_use]
pub mod util;
pub mod dot_writer;
pub mod vtree;

pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
