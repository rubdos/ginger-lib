pub mod big_lazy_merkle_tree;
pub use self::big_lazy_merkle_tree::*;

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum ActionLeaf {
    Insert,
    Remove,
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
// Action associated to the leaf
pub struct OperationLeaf <F: algebra::Field>{
    pub idx: u32,
    pub action: ActionLeaf,
    pub hash: Option<F>,
}

impl<F: algebra::Field> OperationLeaf<F> {
    pub fn new(idx: u32, action: ActionLeaf, hash: Option<F>) -> Self {
        Self { idx, action, hash }
    }
}