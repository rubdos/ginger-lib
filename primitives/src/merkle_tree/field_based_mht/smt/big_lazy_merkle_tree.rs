use crate::{ActionLeaf, Error, crh::{FieldBasedHash, BatchFieldBasedHash, FieldBasedHashParameters}, merkle_tree::{
        MerkleTreeError,    
        field_based_mht::{
            BatchFieldBasedMerkleTreeParameters, check_precomputed_parameters,
            FieldBasedMerkleTreePath, FieldBasedBinaryMHTPath,
            smt::{
                Coord, OperationLeaf,
            },
        },
    }};

use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug)]
pub struct LazyBigMerkleTree<T: BatchFieldBasedMerkleTreeParameters> {
    // the height of this tree
    pub(crate) height: usize,
    // number of leaves
    pub(crate) width: usize,
    // stores the non-empty nodes of the tree
    pub(crate) nodes: HashMap<Coord, T::Data>,
}

impl<T: BatchFieldBasedMerkleTreeParameters> LazyBigMerkleTree<T> {
    /// Creates a new tree of specified `height`.
    pub fn new(
        height: usize,
    ) -> Self 
    {
        assert!(check_precomputed_parameters::<T>(height));

        let rate = <<T::H  as FieldBasedHash>::Parameters as FieldBasedHashParameters>::R;

        assert_eq!(T::MERKLE_ARITY, 2); // For now we support only arity 2
        // Rate may also be smaller than the arity actually, but this assertion
        // is reasonable and simplify the design.
        assert_eq!(rate, T::MERKLE_ARITY);

        // If height is 0 it must not be possible to add any leaf, so we'll set width to 0. 
        let width = if height != 0 { T::MERKLE_ARITY.pow(height as u32) } else { 0 };

        Self {
            height,
            width,
            nodes: HashMap::new(),
        }
    }

    pub fn get_root(&self) -> T::Data {
        self.nodes
            .get(&Coord { height: self.height, idx: 0 })
            .map_or_else(
                || T::ZERO_NODE_CST.unwrap().nodes[self.height], // If not in nodes, then the root is empty
                |&data| data
            )
    }

    /// Used for testing purposes: return (in order) the non empty leaves of the tree
    pub(crate) fn get_non_empty_leaves(&self) -> BTreeMap<Coord, T::Data> {
        let mut sorted_non_empty_leaves = BTreeMap::new();
        self.nodes.iter().for_each(|(coord, data)| {
            if coord.height == 0 {
                sorted_non_empty_leaves.insert(*coord, *data);
            }
        });
        sorted_non_empty_leaves
    }

    pub fn height(&self) -> usize { self.height }

    fn batch_hash(input: &[T::Data]) -> Vec<T::Data> {
        <T::BH as BatchFieldBasedHash>::batch_evaluate(input)
            .expect("Should be able to compute batch hash")
    }

    pub fn is_leaf_empty(&self, idx: usize) -> Result<bool, Error> 
    {
        // check that the index of the leaf is less than the width of the Merkle tree
        if idx >= self.width {
            return Err(MerkleTreeError::IncorrectLeafIndex(idx, format!("Leaf index out of range. Max: {}, got: {}", self.width - 1, idx)))?
        }
        Ok(!self.nodes.contains_key(&Coord { height: 0, idx }))
    }

    pub fn is_tree_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Check and return Error in case of:
    /// - Invalid leaf idx (leaf.coord.idx > self.width);
    /// - Removal of a non existing leaf
    fn pre_check_leaves(&mut self, leaves_map: &mut HashMap<usize, (ActionLeaf, Option<T::Data>)>) -> Result<(), Error> {
        // Collect leaves whose value is set to be empty node
        let mut leaves_to_remove = vec![];

        for (&idx, (action, data)) in leaves_map.iter() {
            
            // Check that the index of the leaf is less than the width of the Merkle tree
            if idx >= self.width {
                if self.height == 0 {
                    return Err(MerkleTreeError::MaximumLeavesReached(0))?
                } else {
                    return Err(MerkleTreeError::IncorrectLeafIndex(idx, format!("Leaf index out of range. Max: {}, got: {}", self.width - 1, idx)))?
                }
            }

            // Forbid attempt to remove a non-existing leaf
            let coord = Coord { height: 0, idx };
            if matches!(action, ActionLeaf::Remove) && (self.is_tree_empty() || !self.nodes.contains_key(&coord)) {
                return Err(MerkleTreeError::IncorrectLeafIndex(coord.idx, format!("Leaf with index {} doesn't exist", coord.idx)))?
            }

            // Save into leaves_to_remove vec if empty node
            if matches!(action, ActionLeaf::Insert) && data.unwrap() == T::ZERO_NODE_CST.unwrap().nodes[0] {
                leaves_to_remove.push(idx);
            }
        }

        // Remove from 'leaves_map' values set to be empty node
        leaves_to_remove.into_iter().for_each(|leaf_idx| { leaves_map.remove(&leaf_idx).unwrap(); });

        Ok(())
    }

    /// Perform insertion/removals of the leaves as specified by 'vec_leaf_op', updates and returns the new root.
    /// This function will return Error in the following situations:
    /// - Invalid leaf idx (leaf.coord.idx > self.width);
    /// - Remove a non existing leaf
    /// Insertion of an already-existing leaf, instead, it's allowed and its value will be simply replaced.
    /// NOTE: Any duplicated leaf coord in 'vec_leaf_op' will be set to its last (ActionLeaf, T::Data) value.
    /// This function is all or nothing: either all the leaves are processed and the tree updated accordingly,
    /// or nothing happens.
    pub fn process_leaves(&mut self, vec_leaf_op: &[OperationLeaf<T::Data>]) -> Result<T::Data, Error> {
        let mut leaves_map = HashMap::new();
        vec_leaf_op
            .iter()
            .for_each(|leaf| { leaves_map.insert(leaf.idx, (leaf.action, leaf.hash)); });
        self.process_unique_leaves(leaves_map)
    }

    fn process_unique_leaves (&mut self, mut leaves_map: HashMap<usize, (ActionLeaf, Option<T::Data>)>) -> Result<T::Data, Error> {

        assert_eq!(T::MERKLE_ARITY, 2, "Arity of the Merkle tree is not 2.");

        // Pre-check leaves to be added
        self.pre_check_leaves(&mut leaves_map)?;

        // Collect nodes to (re)compute for each level of the tree
        let mut nodes_to_process_in_parallel: Vec<HashSet<Coord>> = Vec::with_capacity(self.height);

        // Collect leaves in the first level and contextually add/remove them to/from self.nodes
        let mut leaves = HashSet::<Coord>::new();
        for (idx, (action, data)) in leaves_map.into_iter() {

            // Perform insertion/removal depending on action
            let coord = Coord { height: 0, idx };
            if matches!(action, ActionLeaf::Remove) {
                self.nodes.remove(&coord).unwrap();
            } else {
                self.nodes.insert(coord, data.unwrap());
            }
            leaves.insert(coord);
        }
        nodes_to_process_in_parallel.push(leaves);


        // Find all the nodes that must be recomputed following the
        // additional/removal of leaves
        for height in 0..self.height {
            // Keeps track (uniquely) of the nodes to be processed at the level above
            let mut visited_nodes: HashSet<Coord> = HashSet::new();

            nodes_to_process_in_parallel[height]
                .iter()
                .for_each(|coord| {

                    // Compute parent coord
                    let height_parent = coord.height + 1;
                    let idx_parent = coord.idx / T::MERKLE_ARITY;
                    let parent_coord = Coord { height: height_parent, idx: idx_parent };
                    visited_nodes.insert(parent_coord);
                });

            nodes_to_process_in_parallel.push(visited_nodes);
        }

        // Compute hashes of the affected nodes (ignoring leaf nodes)
        for height in 1..=self.height {
            let mut input_vec = Vec::new(); // Leaves to be hashed
            let mut empty_node = Vec::new(); // Keep track of which node is empty
    
            // Collect leaves to be hashed in parallel
            nodes_to_process_in_parallel[height]
                .iter()
                .for_each(|coord| {    

                    // Compute children coords and get corresponding values
                    let idx = coord.idx;
                    let left_child_idx = idx * T::MERKLE_ARITY;
                    let right_child_idx= left_child_idx + 1;
                    let left_child_coord = Coord { height: coord.height - 1, idx: left_child_idx};
                    let right_child_coord = Coord { height: coord.height - 1, idx: right_child_idx};
        
                    let mut is_node_empty = true;
                    let left_hash = self.nodes
                        .get(&left_child_coord)
                        .map_or_else(
                            || T::ZERO_NODE_CST.unwrap().nodes[height - 1],
                            |&data| {
                                is_node_empty = false;
                                data
                            }
                        );
        
                    let right_hash = self.nodes
                        .get(&right_child_coord)
                        .map_or_else(
                            || T::ZERO_NODE_CST.unwrap().nodes[height - 1],
                            |&data| {
                                is_node_empty = false;
                                data
                            }
                        );
        
                    // Must compute hash iff node will be non-empty, otherwise
                    // we have already its value precomputed
                    if !is_node_empty {
                        input_vec.push(left_hash);
                        input_vec.push(right_hash);
                    } else {
                        // If the node was present in self.nodes we must remove it,
                        // as it has become empty due to some leaf removal operation
                        self.nodes.remove(coord);
                    }
        
                    empty_node.push(is_node_empty);
                });
    
            // Process the input_vec of the nodes that will be non-empty
            // (i.e. the ones who have at least one non-empty children)
            // using batch Poseidon hash
            if !input_vec.is_empty() {
                let output_vec = Self::batch_hash(input_vec.as_slice());
    
                // Update the nodes map with the new values
                let mut output_vec_index = 0;
                for (coord, is_empty) in nodes_to_process_in_parallel[height].iter().zip(empty_node) {
                    if !is_empty {
                        self.nodes.insert(*coord, output_vec[output_vec_index]);
                        output_vec_index += 1;
                    }
                }
            }
        }

        // Return root (which should have been already updated)
        Ok(self.get_root())
    }

    // NB. Allows to get Merkle Path of empty leaves too
    pub fn get_merkle_path(&mut self, idx: usize) -> Result<FieldBasedBinaryMHTPath<T>, Error>
    {
        // check that the index of the leaf is less than the width of the Merkle tree
        if idx >= self.width {
            return Err(MerkleTreeError::IncorrectLeafIndex(idx, format!("Leaf index out of range. Max: {}, got: {}", self.width - 1, idx)))?
        }

        let mut path = Vec::with_capacity(self.height);
        let mut node_idx = idx;
        let mut height = 0;
        while height != self.height {

            // Estabilish if sibling is a left or right child
            let (sibling_idx, direction) = if node_idx % T::MERKLE_ARITY == 0 {
                (node_idx + 1, false)
            } else {
                (node_idx - 1, true)
            };

            // Get its hash
            let sibling_coord = Coord { height, idx: sibling_idx };
            let sibling = self.nodes
                .get(&sibling_coord)
                .map_or_else(
                    || T::ZERO_NODE_CST.unwrap().nodes[height],
                    |&data| data
                );
                
            // Push info to path
            path.push((sibling, direction));

            height += 1; // go up one level
            node_idx = node_idx / T::MERKLE_ARITY; // compute the index of the parent
        }
        assert_eq!(self.nodes.get(&Coord { height, idx: node_idx }).unwrap(), &self.get_root());

        Ok(FieldBasedBinaryMHTPath::<T>::new(path))
    }
}

#[cfg(test)]
mod test {

    use algebra::{
        Field, UniformRand,
    };

    use crate::{
        merkle_tree::field_based_mht::{
            smt::{OperationLeaf, ActionLeaf, LazyBigMerkleTree},
            FieldBasedMerkleTreeParameters, BatchFieldBasedMerkleTreeParameters,
            FieldBasedMerkleTreePath, FieldBasedMerkleTreePrecomputedZeroConstants,
            FieldBasedBinaryMHTPath, FieldBasedMerkleTree, FieldBasedOptimizedMHT,
        }};

    use rand::{Rng, RngCore, prelude::SliceRandom, thread_rng};

    const TEST_HEIGHT: usize = 10;
    const NUM_SAMPLES: usize = 10;

    fn compute_append_only_tree_root<T: BatchFieldBasedMerkleTreeParameters>(
        smt: &LazyBigMerkleTree<T>,
    ) -> T::Data
    {
        let mut optimized = FieldBasedOptimizedMHT::<T>::init(smt.height, smt.width);
        let mut last_idx = 0;
        smt.get_non_empty_leaves().iter().for_each(|(coord, leaf)| {
            for _ in last_idx..coord.idx {
                optimized.append(T::ZERO_NODE_CST.unwrap().nodes[0]).unwrap();
            }
            optimized.append(*leaf).unwrap();
            last_idx = coord.idx + 1;
        });
        optimized.finalize().root().unwrap()
    }

    /// Test correct behavior of the SMT (compared with respect to a FieldBasedOptimizedMHT) by processing batches
    /// of all leaves additions and all leaves removals. If 'adjacent_leaves' is enabled, the batches will be
    /// made up of leaves with subsequent indices
    fn test_batch_all_additions_removals<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: usize,
        rng: &mut R,
        adjacent_leaves: bool,
    ) 
    {
        // Initialize trees
        let mut smt = LazyBigMerkleTree::<T>::new(height);
        let num_leaves = smt.width;

        // Initialize leaves
        let mut leaves = (0..num_leaves)
            .map(|idx| OperationLeaf { idx, action: ActionLeaf::Insert, hash: Some(T::Data::rand(rng)) })
            .collect::<Vec<_>>();

        if !adjacent_leaves {
            leaves.shuffle(rng);
        }

        // Test insertions
        let chunk_size = rng.gen_range(1, num_leaves + 1);
        leaves
            .chunks(chunk_size)
            .for_each(|leaves| {
                // Insert all leaves into smt and get root
                let smt_root = smt.process_leaves(leaves).unwrap();

                // Insert into optimized and get root
                let optimized_root = compute_append_only_tree_root(&mut smt);

                // Roots must be equal
                assert_eq!(smt_root, optimized_root, "Roots are not equal");
            });
        
        // Nodes map must be full
        assert_eq!(smt.nodes.len(), (num_leaves * 2) - 1);


        // Test removals
        // Remove all leaves and update smt
        leaves
            .iter_mut()
            .for_each(|leaf| leaf.action = ActionLeaf::Remove);

        leaves
            .chunks(chunk_size)
            .for_each(|leaves_chunk| {
                // Remove leaves from smt and get root
                let smt_root = smt.process_leaves(leaves_chunk).unwrap();

                // "Remove" from optimized and get root
                let optimized_root = compute_append_only_tree_root(&mut smt);

                // Roots must be equal
                assert_eq!(smt_root, optimized_root, "Roots are not equal");
        });

        // In the end, we must have an empty root...
        assert_eq!(smt.get_root(), T::ZERO_NODE_CST.unwrap().nodes[height], "Root after removal of all leaves must be equal to empty root");

        // ...and nodes map must be empty
        assert!(smt.nodes.is_empty());
    }

    /// Test correct behavior of the SMT (compared with respect to a FieldBasedOptimizedMHT) by processing batches
    /// of leaves additions and removals, in mixed order.
    fn test_batch_mixed_additions_removals<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: usize,
        rng: &mut R,
    ) 
    {
        // Initialize trees: fill half of the SMT
        let mut smt = LazyBigMerkleTree::<T>::new(height);
        let num_leaves = smt.width;
        let mut leaves = (0..num_leaves/2)
            .map(|idx| OperationLeaf { idx, action: ActionLeaf::Insert, hash: Some(T::Data::rand(rng)) })
            .collect::<Vec<_>>();
        let _ = smt.process_leaves(leaves.as_slice());

        // Test batches of mixed insertions/removals: fill the other half of the tree and remove the first half.

        // Remove previously inserted leaves
        leaves
            .iter_mut()
            .for_each(|leaf| (*leaf).action = ActionLeaf::Remove);

        // Fill the other half of the tree
        leaves.append(
            &mut (num_leaves/2..num_leaves)
                .map(|idx| OperationLeaf { idx, action: ActionLeaf::Insert, hash: Some(T::Data::rand(rng)) })
                .collect::<Vec<_>>()
        );

        // Mix the leaves
        leaves.shuffle(rng);

        // Test
        let chunk_size = rng.gen_range(1, num_leaves + 1);
        leaves
            .chunks(chunk_size)
            .for_each(|leaves| {
                let smt_root = smt.process_leaves(leaves).unwrap();
                let optimized_root = compute_append_only_tree_root(&mut smt);
                assert_eq!(smt_root, optimized_root, "Roots are not equal");
            });
        
        // Nodes map must be half full
        assert_eq!(smt.nodes.len(), num_leaves);
    }

    fn test_error_cases<T: BatchFieldBasedMerkleTreeParameters>(
        height: usize,
    ) {
        // Initialize tree
        let mut smt = LazyBigMerkleTree::<T>::new(height);
        
        let mut dummy_leaf = OperationLeaf::new(0, ActionLeaf::Remove, Some(T::Data::one()));
        
        // Remove leaf from an empty tree
        assert!(smt.process_leaves(&[dummy_leaf]).unwrap_err().to_string().contains("Leaf with index 0 doesn't exist"));

        // Remove a leaf out of range
        dummy_leaf.idx = smt.width;
        assert!(smt.process_leaves(&[dummy_leaf]).unwrap_err().to_string().contains(format!("Leaf index out of range. Max: {}, got: {}", smt.width - 1, smt.width).as_str()));

        // Add a leaf out of range
        dummy_leaf.action = ActionLeaf::Insert;
        assert!(smt.process_leaves(&[dummy_leaf]).unwrap_err().to_string().contains(format!("Leaf index out of range. Max: {}, got: {}", smt.width - 1, smt.width).as_str()));

        // Add a correct leaf
        dummy_leaf.idx -= 1;
        let smt_root = smt.process_leaves(&[dummy_leaf]).unwrap();
        assert_eq!(smt_root, compute_append_only_tree_root(&smt));
        assert_eq!(smt.nodes.len(), height + 1);

        // Replace previously added leaf with a new value and check correct replacement
        dummy_leaf.hash = Some(T::Data::from(2u8));
        let new_smt_root = smt.process_leaves(&[dummy_leaf]).unwrap();
        assert_ne!(new_smt_root, smt_root);
        assert_eq!(new_smt_root, compute_append_only_tree_root(&smt));
        assert_eq!(smt.nodes.len(), height + 1);

        // Remove non existing leaf with non full tree
        dummy_leaf.idx -= 1;
        dummy_leaf.action = ActionLeaf::Remove;
        assert!(smt.process_leaves(&[dummy_leaf]).unwrap_err().to_string().contains(format!("Leaf with index {} doesn't exist", smt.width - 2).as_str()));

        // Remove leaf
        dummy_leaf.idx += 1;
        dummy_leaf.action = ActionLeaf::Remove;

        // Tree must be empty now
        assert_eq!(smt.process_leaves(&[dummy_leaf]).unwrap(), T::ZERO_NODE_CST.unwrap().nodes[height]);
        assert!(smt.nodes.is_empty());

        // Add multiple times the same leaf: only last value of the leaf shall be taken
        {
            let mut leaves = (0..=NUM_SAMPLES)
                .map(|i| OperationLeaf::new(0, ActionLeaf::Insert, Some(T::Data::from(i as u8))))
                .collect::<Vec<_>>();
            
            let smt_root = smt.process_leaves(leaves.as_slice()).unwrap();
            assert_eq!(smt.nodes.len(), height + 1);

            let optimized_root = FieldBasedOptimizedMHT::<T>::init(smt.height, smt.width)
                .append(T::Data::from(NUM_SAMPLES as u8))
                .unwrap()
                .finalize()
                .root()
                .unwrap();

            assert_eq!(smt_root, optimized_root);

            // If we append a leaf removal at the end, again, only this last removal will be taken into account
            leaves.push(OperationLeaf::new(0, ActionLeaf::Remove, Some(T::Data::from((NUM_SAMPLES + 1) as u8))));
            let smt_root = smt.process_leaves(leaves.as_slice()).unwrap();

            // Tree must be empty now
            assert_eq!(smt_root, T::ZERO_NODE_CST.unwrap().nodes[height]);
            assert!(smt.nodes.is_empty());
        }

        // Test that if some error occurs during the processing of a batch of leaves, the tree state will be untouched.
        {
            // Valid leaves to be added
            let mut leaves = (0..=NUM_SAMPLES)
                .map(|i| OperationLeaf::new(i, ActionLeaf::Insert, Some(T::Data::from(i as u8))))
                .collect::<Vec<_>>();

            // Let's add an out-of-range leaf at the end to trigger an error
            leaves.push(OperationLeaf::new(smt.width, ActionLeaf::Insert, Some(T::Data::from(NUM_SAMPLES as u8))));

            assert!(smt.process_leaves(leaves.as_slice()).unwrap_err().to_string().contains(format!("Leaf index out of range. Max: {}, got: {}", smt.width - 1, smt.width).as_str()));

            // Tree must be empty as before
            assert_eq!(smt.get_root(), T::ZERO_NODE_CST.unwrap().nodes[height]);
            assert!(smt.nodes.is_empty());
        }

        // Finally, let's test that manually adding empty leaves results in a no-op
        {
            let leaves = (0..=NUM_SAMPLES)
                .map(|i| OperationLeaf::new(i, ActionLeaf::Insert, Some(T::ZERO_NODE_CST.unwrap().nodes[0])))
                .collect::<Vec<_>>();

            // Tree must be empty as before
            assert_eq!(smt.process_leaves(leaves.as_slice()).unwrap(), T::ZERO_NODE_CST.unwrap().nodes[height]);
            assert!(smt.nodes.is_empty());
        }
    }

    fn test_edge_cases<T: BatchFieldBasedMerkleTreeParameters>() {
        let dummy_leaf = OperationLeaf::new(0, ActionLeaf::Insert, Some(T::Data::one()));

        // HEIGHT > 1
        {
            // Generate empty tree and get the root
            let mut smt = LazyBigMerkleTree::<T>::new(TEST_HEIGHT);
            let root = smt.get_root();
            assert_eq!(root, T::ZERO_NODE_CST.unwrap().nodes[TEST_HEIGHT]);

            // Generate tree with only 1 leaf and attempt to get the root
            assert!(smt.process_leaves(&[dummy_leaf]).is_ok());
            let new_root = smt.get_root();
            assert_ne!(new_root, root);
            assert_ne!(new_root, T::ZERO_NODE_CST.unwrap().nodes[TEST_HEIGHT]);
        }

        // HEIGHT == 1
        {
            // Generate empty tree and get the root
            let mut smt = LazyBigMerkleTree::<T>::new(1);
            let mut root = smt.get_root();
            assert_eq!(root, T::ZERO_NODE_CST.unwrap().nodes[1]);

            // Generate tree with only 1 leaf and attempt to get the root
            assert!(smt.process_leaves(&[dummy_leaf]).is_ok());
            let new_root = smt.get_root();
            assert_ne!(new_root, root);
            assert_ne!(new_root, T::ZERO_NODE_CST.unwrap().nodes[1]);
            root = new_root;

            // Generate tree with exactly 2 leaves and attempt to get the root.
            // Assert error if trying to add another leaf
            assert!(smt.process_leaves(&[OperationLeaf::new(1, ActionLeaf::Insert, Some(T::Data::one()))]).is_ok());
            let new_root = smt.get_root();
            assert_ne!(new_root, root);
            assert_ne!(new_root, T::ZERO_NODE_CST.unwrap().nodes[1]);

            assert!(smt.process_leaves(&[OperationLeaf::new(2, ActionLeaf::Insert, Some(T::Data::one()))]).is_err());
        }

        // HEIGHT == 0
        {
            // Generate empty tree and get the root
            let mut smt = LazyBigMerkleTree::<T>::new(0);
            let root = smt.get_root();
            assert_eq!(root, T::ZERO_NODE_CST.unwrap().nodes[0]);

            // Generate tree with only 1 leaf and assert error
            assert!(smt.process_leaves(&[dummy_leaf]).unwrap_err().to_string().contains("Reached maximum number of leaves for a tree of height 0"));
        }
    }

    fn test_merkle_path<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: usize,
        rng: &mut R,
    ) {
        let mut smt = LazyBigMerkleTree::<T>::new(height);
        let num_leaves = smt.width;
        let mut optimized = FieldBasedOptimizedMHT::<T>::init(smt.height, num_leaves);
        let mut leaves_for_lazy_smt = Vec::with_capacity(num_leaves);

        // Generate random leaves, half of which empty
        for i in 0..num_leaves/2 {
            let leaf = T::Data::rand(rng);
            optimized.append(leaf).unwrap();
            leaves_for_lazy_smt.push(OperationLeaf { idx: i, action: ActionLeaf::Insert, hash: Some(leaf)});
        }
        optimized.finalize_in_place();

        // Compute the root of the tree, and do the same for a FieldBasedOptimizedMHT, used here as reference
        let root = smt.process_leaves(leaves_for_lazy_smt.as_slice()).unwrap();
        let optimized_root = optimized.root().unwrap();
        assert_eq!(root, optimized_root);

        for (i, leaf) in optimized.get_leaves().iter().enumerate() {

            // Create and verify a FieldBasedMHTPath
            let path = smt.get_merkle_path(i).unwrap();
            assert!(path.verify(smt.height(), leaf, &root).unwrap());

            // Create and verify a path from FieldBasedOptimizedMHT
            let optimized_path = optimized.get_merkle_path(i).unwrap();
            assert!(optimized_path.verify(optimized.height(), leaf, &optimized_root).unwrap());

            // Assert the two paths are equal
            let optimized_path: FieldBasedBinaryMHTPath<T> = optimized_path.into();
            assert_eq!(optimized_path, path);

            // Check leaf index is the correct one
            assert_eq!(i, path.leaf_index());

            if i == 0 { assert!(path.is_leftmost()); } // leftmost check
            else if i == num_leaves - 1 { assert!(path.is_rightmost()) }  //rightmost check
            else { assert!(!path.is_leftmost()); assert!(!path.is_rightmost()); } // other cases check

            // Serialization/deserialization test
            algebra::serialize::test_canonical_serialize_deserialize(true, &path);
        }
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_tweedle_fr() {
        use algebra::fields::tweedle::Fr;
        use crate::{
            crh::{TweedleFrPoseidonHash, TweedleFrBatchPoseidonHash},
            merkle_tree::TWEEDLE_DEE_MHT_POSEIDON_PARAMETERS,
        };

        #[derive(Clone, Debug)]
        struct TweedleFrFieldBasedMerkleTreeParams;
        impl FieldBasedMerkleTreeParameters for TweedleFrFieldBasedMerkleTreeParams {
            type Data = Fr;
            type H = TweedleFrPoseidonHash;
            const MERKLE_ARITY: usize = 2;
            const ZERO_NODE_CST: Option<FieldBasedMerkleTreePrecomputedZeroConstants<'static, Self::H>> =
                Some(TWEEDLE_DEE_MHT_POSEIDON_PARAMETERS);
        }
        impl BatchFieldBasedMerkleTreeParameters for TweedleFrFieldBasedMerkleTreeParams {
            type BH = TweedleFrBatchPoseidonHash;
        }

        let rng = &mut thread_rng();
        for _ in 0..NUM_SAMPLES {
            test_batch_all_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(TEST_HEIGHT, rng, true);
            test_batch_all_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(TEST_HEIGHT, rng, false);
            test_batch_mixed_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(TEST_HEIGHT, rng);
        }
        test_merkle_path::<TweedleFrFieldBasedMerkleTreeParams, _>(TEST_HEIGHT, rng);
        test_error_cases::<TweedleFrFieldBasedMerkleTreeParams>(TEST_HEIGHT);
        test_edge_cases::<TweedleFrFieldBasedMerkleTreeParams>();
    }
}