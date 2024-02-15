pub struct VTree {
    // TODO: Search states, shadow vtree.
    left: Option<Box<VTree>>,
    right: Option<Box<VTree>>,
}

impl VTree {
    pub fn new(left: Option<Box<VTree>>, right: Option<Box<VTree>>) -> VTree {
        VTree { left, right }
    }

    // right-linear fragment:
    //         X
    //        / \
    //       Y   Z
    //          / \
    //         G   D
    // idea: cycle through all the 12 different configurations of the right-linear fragment using rotations and swapping.
    //  => fragment operations: next, previous, goto
    //  => greedy search for better vtree when the SDD is too large:
    //     - enumerate all (24 = 12 + 12) vtrees over a window
    //     - greedily accept best vtree, move window

    // Explore dissections but not all possible vtrees,
    // since it's not possible to explore different variable orders because rotations preserve the order of the variables.
    // TODO: For systematic methods check 'Art of Computer Programming, Volume 4, Fascicle 4: Generating all Tree'
    pub fn right_rotate(&self) {}

    // Explore dissections but not all possible vtrees,
    // since it's not possible to explore different variable orders because rotations preserve the order of the variables.
    // TODO: For systematic methods check 'Art of Computer Programming, Volume 4, Fascicle 4: Generating all Tree'
    pub fn left_rotate(&self) {}

    // TODO: Is swapping done only on siblings? What about swapping a leaf with its cousin? Seems so.
    // Dynamic Minimization of Sentential Decision Diagrams paper.
    pub fn swap(&self) {}

    // fragment operations: next, previous, goto
    pub fn next() {}
    pub fn previous() {}
    pub fn goto() {}
}

pub struct VTreeManager {
    root: Option<VTree>,

    dfs_to_bfs: Vec<u64>,
    bfs_to_dfs: Vec<u64>,
}

impl VTreeManager {
    pub fn new() -> VTreeManager {
        VTreeManager {
            root: None,
            dfs_to_bfs: Vec::new(),
            bfs_to_dfs: Vec::new(),
        }
    }
}
