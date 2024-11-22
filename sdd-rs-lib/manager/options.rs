use bon::Builder;
use clap::ValueEnum;

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum InitialVTree {
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
#[derive(Debug, Clone, Copy, Builder)]
pub struct SddOptions {
    pub initial_vtree: InitialVTree,
    pub fragment_heuristic: FragmentHeuristic,
    pub minimize_after: usize,
    pub minimization_cutoff: MinimizationCutoff,
}

impl Default for SddOptions {
    #[must_use]
    fn default() -> Self {
        SddOptions {
            initial_vtree: InitialVTree::Balanced,
            fragment_heuristic: FragmentHeuristic::Root,
            minimize_after: 0,
            minimization_cutoff: MinimizationCutoff::None,
        }
    }
}

impl SddOptions {
    #[must_use]
    pub fn new() -> SddOptions {
        SddOptions::default()
    }

    pub fn set_initial_vtree(&mut self, initial_vtree: InitialVTree) -> &mut Self {
        self.initial_vtree = initial_vtree;
        self
    }
}
