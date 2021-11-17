#[macro_use]
extern crate criterion;

use std::collections::HashSet;

use criterion::{BatchSize, BenchmarkId, Criterion};
use algebra::{UniformRand, fields::tweedle::Fr};
use primitives::{ActionLeaf, OperationLeaf, crh::{TweedleFrPoseidonHash, TweedleFrBatchPoseidonHash}, merkle_tree::{
        TWEEDLE_DEE_MHT_POSEIDON_PARAMETERS, FieldBasedMerkleTreeParameters, BatchFieldBasedMerkleTreeParameters,
        FieldBasedMerkleTreePrecomputedZeroConstants, LazyBigMerkleTree
    }};
use rand::{Rng, thread_rng};

const BENCH_HEIGHT: u8 = 22;

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

/// Add to the tree 'num_leaves_to_fill' random leaves in leftmost subsequent positions.
/// Then sample 'num_leaves_to_remove' leaves, among the ones added before, to remove.
/// Then return such leaves.
/// If 'actually_remove_leaves' is set, the leaves are actually removed from the SMT
/// and changed to insertion mode before returning.
fn fill_tree_and_get_leaves_to_remove(
    smt: &mut LazyBigMerkleTree<TweedleFrFieldBasedMerkleTreeParams>,
    num_leaves_to_fill: usize,
    num_leaves_to_remove: usize,
    actually_remove_leaves: bool,
) -> Vec<OperationLeaf<Fr>> 
{
    // Generate leaves to be added
    let rng = &mut thread_rng();
    let leaves_to_add = (0..num_leaves_to_fill)
        .map(|idx| OperationLeaf::new(idx as u32, ActionLeaf::Insert, Some(Fr::rand(rng))))
        .collect::<Vec<_>>();
    smt.process_leaves(leaves_to_add.as_slice()).unwrap();

    // Collect leaves to remove randomly among the ones already present in the tree
    let mut leaves_to_remove = HashSet::<u32>::new();
    while leaves_to_remove.len() != num_leaves_to_remove {
        let idx = rng.gen_range(0..num_leaves_to_fill) as u32;
        if !leaves_to_remove.contains(&idx) {
            leaves_to_remove.insert(idx as u32);
        }
    }

    // Convert HashSet into vec
    let mut leaves_to_remove: Vec<OperationLeaf<Fr>> = leaves_to_remove
        .into_iter()
        .map(|idx| OperationLeaf::<Fr>::new(idx, ActionLeaf::Remove, None))
        .collect();

    if actually_remove_leaves {
        smt.process_leaves(leaves_to_remove.as_slice()).unwrap();
        leaves_to_remove
            .iter_mut()
            .for_each(|leaf|{
                (*leaf).action = ActionLeaf::Insert;
                (*leaf).hash = Some(Fr::rand(rng))
            });
    }

    leaves_to_remove
}

fn bench_batch_addition_removal_smt(
    c: &mut Criterion,
    bench_name: &str,
    leaves_to_fill: usize,
    actually_remove_leaves: bool,
) {
    let mut group = c.benchmark_group(bench_name);

    let num_leaves_samples = (5..=12).map(|i| 1 << i).collect::<Vec<_>>();

    for num_leaves in num_leaves_samples {
        group.bench_with_input(
            BenchmarkId::from_parameter(num_leaves),
            &num_leaves,
            |b, _num_leaves| {
                b.iter_batched(
                    || {
                        let mut smt = LazyBigMerkleTree::<TweedleFrFieldBasedMerkleTreeParams>::new(BENCH_HEIGHT);
                        let leaves_to_remove = fill_tree_and_get_leaves_to_remove(&mut smt, leaves_to_fill, num_leaves, actually_remove_leaves);
                        (smt, leaves_to_remove)
                    },
                    |(mut smt, leaves)| {
                        smt.process_leaves(leaves.as_slice())
                    },
                    BatchSize::PerIteration,
                );
            },
        );
    }
}

/// Add to the tree 'num_leaves_to_fill' random leaves in leftmost subsequent positions.
/// Then sample 'num_leaves_to_add' leaves and insert them after the ones already present
/// in the tree.
/// If 'subsequent' is set, the leaves will be generated with contiguous indices.
fn fill_tree_and_add_new(
    smt: &mut LazyBigMerkleTree<TweedleFrFieldBasedMerkleTreeParams>,
    mut num_leaves_to_fill: usize,
    num_leaves_to_add: usize,
    subsequent: bool,
) -> Vec<OperationLeaf<Fr>> 
{
    // Generate leaves to be added
    let rng = &mut thread_rng();
    let leaves_to_add = (0..num_leaves_to_fill)
        .map(|idx| OperationLeaf::new(idx as u32, ActionLeaf::Insert, Some(Fr::rand(rng))))
        .collect::<Vec<_>>();
    smt.process_leaves(leaves_to_add.as_slice()).unwrap();

    // Collect leaves to add randomly
    let mut leaves_to_add = HashSet::<u32>::new();
    while leaves_to_add.len() != num_leaves_to_add {
        let idx = if !subsequent {
            rng.gen_range(num_leaves_to_fill..1 << BENCH_HEIGHT) as u32
        } else {
            let idx = num_leaves_to_fill;
            num_leaves_to_fill += 1;
            idx as u32
        };

        if !leaves_to_add.contains(&idx) {
            leaves_to_add.insert(idx as u32);
        }
    }

    // Convert HashSet into vec
    let mut leaves_to_add: Vec<OperationLeaf<Fr>> = leaves_to_add
        .into_iter()
        .map(|idx| OperationLeaf::<Fr>::new(idx, ActionLeaf::Insert, Some(Fr::rand(rng))))
        .collect();

    leaves_to_add
}

fn bench_batch_addition(
    c: &mut Criterion,
    bench_name: &str,
    leaves_to_fill: usize,
    subsequent: bool
) 
{
    let mut group = c.benchmark_group(bench_name);

    let num_leaves_samples = (5..=12).map(|i| 1 << i).collect::<Vec<_>>();

    for num_leaves in num_leaves_samples {
        group.bench_with_input(
            BenchmarkId::from_parameter(num_leaves),
            &num_leaves,
            |b, _num_leaves| {
                b.iter_batched(
                    || {
                        let mut smt = LazyBigMerkleTree::<TweedleFrFieldBasedMerkleTreeParams>::new(BENCH_HEIGHT);
                        let leaves_to_add = fill_tree_and_add_new(&mut smt, leaves_to_fill, num_leaves, subsequent);
                        (smt, leaves_to_add)
                    },
                    |(mut smt, leaves)| {
                        smt.process_leaves(leaves.as_slice())
                    },
                    BatchSize::PerIteration,
                );
            },
        );
    }
}

fn all_benches_batch_remove(c: &mut Criterion) {
    bench_batch_addition_removal_smt(c, "almost empty tree - remove batch", (1 << BENCH_HEIGHT as usize)/10, false);
    bench_batch_addition_removal_smt(c, "half full tree - remove batch", (1 << BENCH_HEIGHT as usize)/2, false);
    bench_batch_addition_removal_smt(c, "almost full tree - remove batch", (9 * (1 << BENCH_HEIGHT as usize))/10, false);
}

fn all_benches_batch_remove_then_add(c: &mut Criterion) {
    bench_batch_addition_removal_smt(c, "almost empty tree - remove then add batch", (1 << BENCH_HEIGHT as usize)/10, true);
    bench_batch_addition_removal_smt(c, "half full tree - remove then add batch", (1 << BENCH_HEIGHT as usize)/2, true);
    bench_batch_addition_removal_smt(c, "almost full tree - remove then add batch", (9 * (1 << BENCH_HEIGHT as usize))/10, true);
}

fn all_benches_batch_add(c: &mut Criterion) {
    bench_batch_addition(c, "almost empty tree - add batch random idx", (1 << BENCH_HEIGHT as usize)/10, false);
    bench_batch_addition(c, "half full tree - add batch random idx", (1 << BENCH_HEIGHT as usize)/2, false);
    bench_batch_addition(c, "almost full tree - add batch random idx", (9 * (1 << BENCH_HEIGHT as usize))/10, false);
}

fn all_benches_batch_add_subsequent(c: &mut Criterion) {
    bench_batch_addition(c, "almost empty tree - add batch subsequent idx", (1 << BENCH_HEIGHT as usize)/10, true);
    bench_batch_addition(c, "half full tree - add batch subsequent idx", (1 << BENCH_HEIGHT as usize)/2, true);
    bench_batch_addition(c, "almost full tree - add batch subsequent idx", (9 * (1 << BENCH_HEIGHT as usize))/10, true);
}

criterion_group! {
    name = in_memory_smt_tweedle_fr;
    config = Criterion::default().sample_size(10);
    targets = all_benches_batch_remove_then_add, all_benches_batch_remove, all_benches_batch_add, all_benches_batch_add_subsequent
}

criterion_main!(in_memory_smt_tweedle_fr);