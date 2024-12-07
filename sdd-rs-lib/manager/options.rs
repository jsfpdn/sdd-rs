use bon::Builder;
use clap::ValueEnum;

use crate::vtree::{Linearity, VTreeIdx};

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum VTreeStrategy {
    Balanced,
    LeftLinear,
    RightLinear,
}

/// Describes how to pick a fragment in order to dynamically minimize SDDs.
#[derive(Debug, Clone, Copy)]
pub enum FragmentHeuristic {
    /// Root of the fragment is vtree node `v` for which the most
    /// SDDs are normalized. A child of this fragment is a
    /// child of the `v` node for which more SDDs are normalized.
    MostNormalized,
    /// Pick a random internal vtree node. If its right child
    /// is an intenral node, the fragment is right-linear.
    /// It is left-linear otherwise.
    Random,
    /// Choose the root of the vtree as root of the fragment.
    /// If its right child is an internal node, the fragment is
    /// right-linear. It is left-linear otherwise.
    Root,
    /// Chooses vtree node with [`VTreeIdx`] as the root of the
    /// fragment and makes it either left-linear or right-linear.
    Custom(VTreeIdx, Linearity),
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
    Decrease(f64),
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

    #[builder(into)]
    pub variables: Vec<String>,

    #[builder(default = GarbageCollection::Automatic(0.3))]
    pub garbage_collection: GarbageCollection,
}
