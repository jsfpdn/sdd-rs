use bon::Builder;
use clap::ValueEnum;

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum VTreeStrategy {
    Balanced,
    LeftLinear,
    RightLinear,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum FragmentHeuristic {
    Random,
    Root,
}

#[derive(Debug, Clone, Copy)]
pub enum GarbageCollection {
    Off,
    Automatic(f64),
}

#[derive(Debug, Clone, Copy)]
pub enum MinimizationCutoff {
    None,
    Iteration(usize),
    Decrease(f32),
    // TODO: Add variant for time elapsed.
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Builder)]
pub struct SddOptions {
    #[builder(default = VTreeStrategy::Balanced)]
    pub vtree_strategy: VTreeStrategy,

    #[builder(default = FragmentHeuristic::Root)]
    pub fragment_heuristic: FragmentHeuristic,

    #[builder(default = 0)]
    pub minimize_after: usize,

    #[builder(default = MinimizationCutoff::None)]
    pub minimization_cutoff: MinimizationCutoff,

    #[builder(default = Vec::new())]
    #[builder(into)]
    pub variables: Vec<String>,

    #[builder(default = GarbageCollection::Automatic(0.3))]
    pub garbage_collection: GarbageCollection,
}

/// TODO: This is an ugly hack, fix it.
pub fn vars(variables: Vec<&str>) -> Vec<String> {
    variables.iter().map(|v| v.to_string()).collect()
}
