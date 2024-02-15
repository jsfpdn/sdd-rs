use crate::options::{GcSchedule, InitialVTree, SddOptions, VTreeStrategy};

pub mod options;
pub mod sdd;
pub mod structs;
pub mod vtree;

fn main() {
    let options = SddOptions::default()
        .set_gc_schedule(GcSchedule::Automatic(1120))
        .set_gc_strategy(VTreeStrategy::Cycle)
        .set_initial_vtree(InitialVTree::Balanced)
        .to_owned();

    #[allow(unused)]
    let mut manager = sdd::SDDManager::new(options);
}
