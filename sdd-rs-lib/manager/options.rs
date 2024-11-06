#[derive(Debug, Clone, Copy)]
pub enum InitialVTree {
    Balanced,
    LeftLinear,
    RightLinear,
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug, Clone, Copy)]
pub struct SddOptions {
    initial_vtree: InitialVTree,
}

impl Default for SddOptions {
    #[must_use]
    fn default() -> Self {
        SddOptions {
            initial_vtree: InitialVTree::Balanced,
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
