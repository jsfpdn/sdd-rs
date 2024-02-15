#[derive(Debug, Clone, Copy)]
pub enum GcSchedule {
    Manual,
    Automatic(usize), // usize denotes the threshold when the GC would be triggered
}

#[derive(Debug, Clone, Copy)]
pub enum VTreeStrategy {
    Custom(()), // TODO: Add type for custom function that will manipulate vtrees when GC is triggered
    Cycle, // This is the "default" strategy in the original C SDD library that cycles through all vtrees within the given resources.
}

#[derive(Debug, Clone, Copy)]
pub enum InitialVTree {
    Balanced,
    LeftLinear,
    RightLinear,
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy)]
pub struct SDDOptions {
    gc_schedule: GcSchedule,

    vtree_strategy: VTreeStrategy,
    initial_vtree: InitialVTree,
}

impl Default for SDDOptions {
    #[must_use]
    fn default() -> Self {
        SDDOptions {
            gc_schedule: GcSchedule::Automatic(1000),

            vtree_strategy: VTreeStrategy::Cycle,
            initial_vtree: InitialVTree::Balanced,
        }
    }
}

impl SDDOptions {
    #[must_use]
    pub fn new() -> SDDOptions {
        SDDOptions::default()
    }

    pub fn set_gc_strategy(&mut self, strategy: VTreeStrategy) -> &mut Self {
        self.vtree_strategy = strategy;
        self
    }

    pub fn set_gc_schedule(&mut self, schedule: GcSchedule) -> &mut Self {
        self.gc_schedule = schedule;
        self
    }

    pub fn set_initial_vtree(&mut self, initial_vtree: InitialVTree) -> &mut Self {
        self.initial_vtree = initial_vtree;
        self
    }
}
