#[macro_use]
extern crate criterion;

use algebra::curves::mnt4753::G1Projective as MNT4Projective;
use criterion::Criterion;
use primitives::crh::{pedersen::*, FixedLengthCRH};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct HashWindow;

impl PedersenWindow for HashWindow {
    const WINDOW_SIZE: usize = 250;
    const NUM_WINDOWS: usize = 8;
}

fn pedersen_crh_setup(c: &mut Criterion) {
    c.bench_function("Pedersen CRH Setup", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            PedersenCRH::<MNT4Projective, HashWindow>::setup(&mut rng).unwrap()
        })
    });
}

fn pedersen_crh_eval(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let parameters = PedersenCRH::<MNT4Projective, HashWindow>::setup(&mut rng).unwrap();
    let input = vec![5u8; 128];
    c.bench_function("Pedersen CRH Eval", move |b| {
        b.iter(|| {
            PedersenCRH::<MNT4Projective, HashWindow>::evaluate(&parameters, &input).unwrap();
        })
    });
}

criterion_group! {
    name = crh_setup;
    config = Criterion::default().sample_size(20);
    targets = pedersen_crh_setup
}

criterion_group! {
    name = crh_eval;
    config = Criterion::default().sample_size(20);
    targets = pedersen_crh_eval
}

criterion_main!(crh_setup, crh_eval);
