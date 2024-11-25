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
pub enum MinimizationCutoff {
    None,
    Iteration(usize),
    Decrease(f32),
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Builder)]
pub struct SddOptions {
    pub vtree_strategy: VTreeStrategy,
    pub fragment_heuristic: FragmentHeuristic,
    pub minimize_after: usize,
    pub minimization_cutoff: MinimizationCutoff,
    pub variables: Vec<String>,
}

impl Default for SddOptions {
    #[must_use]
    fn default() -> Self {
        SddOptions {
            vtree_strategy: VTreeStrategy::Balanced,
            fragment_heuristic: FragmentHeuristic::Root,
            minimize_after: 0,
            minimization_cutoff: MinimizationCutoff::None,
            variables: Vec::new(),
        }
    }
}
