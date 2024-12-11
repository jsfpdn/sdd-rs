use bon::Builder;
use clap::ValueEnum;

use crate::vtree::Fragment;

/// How to construct an initial vtree.
#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum VTreeStrategy {
    /// Construct a balanced vtree -- each leaf has the same depth.
    Balanced,
    /// Construct a left-linear vtree -- each right child is a leaf.
    LeftLinear,
    /// Construct a right-linear vtree -- each left child is a leaf.
    RightLinear,
}

/// Describes how to pick a fragment in order to dynamically minimize SDDs.
#[derive(Debug, Clone)]
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
    Custom(Fragment),
}

/// Whether to automatically collect garbage.
#[derive(Debug, Clone, Copy)]
pub enum GarbageCollection {
    /// Does not automatically collect garbage.
    Off,
    /// Collects garbage automatically every time
    /// SDDs are combined with some operation.
    Automatic,
}

/// Denotes when to stop searching for better vtree fragment
/// states when dynamically minimizing SDDs.
#[derive(Debug, Clone, Copy)]
pub enum MinimizationCutoff {
    /// Does not stop and explores all 12 fragment states.
    None,
    /// Stops after i-th iteration.
    Iteration(usize),
    /// Stops after decrease in size of a referential SDD reaches given threshold:
    /// `size(after)/size(before) <= threshold`. Therefore, if size of SDD drops
    /// from 150 to 100 and the threshold is set to 0.8, the search terminates
    /// since `100/150 = 0.66 <= 0.8`.
    Decrease(f64),
}

/// [`sddrs::manager::SddManager`] configuration options. See individual
/// fields for more information.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Builder)]
pub struct SddOptions {
    /// How to build initial vtree.
    #[builder(default = VTreeStrategy::Balanced)]
    pub vtree_strategy: VTreeStrategy,

    /// How to pick a vtree fragment for dynamic minimization, if dynamic
    /// minimization is enabled.
    #[builder(default = FragmentHeuristic::MostNormalized)]
    pub fragment_heuristic: FragmentHeuristic,

    /// When compiling Boolean function from a DIMACS, dynamically minimize
    /// after every `k` clauses. `k` set to 0 means never.
    #[builder(default = 0)]
    pub minimize_after: usize,

    /// When to stop searching for better vtree fragment state, if dynamic
    /// minimization is enabled.
    #[builder(default = MinimizationCutoff::None)]
    pub minimization_cutoff: MinimizationCutoff,

    /// Variables to be used when compiling knowledge. This is a static
    /// set of variables and cannot be changed later.
    #[builder(into)]
    pub variables: Vec<String>,

    /// Whether to automatically trigger garbage collection of dead nodes.
    #[builder(default = GarbageCollection::Automatic)]
    pub garbage_collection: GarbageCollection,

    /// When rewinding fragment state during dynamic minimization, whether
    /// to settle for "good-enough" states on our way to the best state
    /// instead of rolling back to the best one. In certain (most) cases,
    /// searching over fragment and rewinding is expensive. This saves us
    /// some time by settling for "good-enough" states instead of going
    /// back all the way to the best one discovered.
    #[builder(default = false)]
    pub imprecise_rewind: bool,
}
