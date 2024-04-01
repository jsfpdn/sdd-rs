use sddrs::manager::SddManager;
use sddrs::options::{GcSchedule, InitialVTree, SddOptions, VTreeStrategy};

fn main() {
    let options = SddOptions::default()
        .set_gc_schedule(GcSchedule::Automatic(1120))
        .set_gc_strategy(VTreeStrategy::Cycle)
        .set_initial_vtree(InitialVTree::Balanced)
        .to_owned();

    #[allow(unused)]
    let mut manager = SddManager::new(options);
}
