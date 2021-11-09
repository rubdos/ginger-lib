use algebra::fields::ed25519::{fq::Fq as ed25519Fq, fr::Fr as ed25519Fr};
use algebra::serialize::*;
use algebra::{
    curves::tweedle::dee::Affine as DeeAffine, fields::tweedle::Fr as TweedleFr, AffineCurve, Field,
};
use algebra::{PrimeField, ToBits, UniformRand};
use marlin::Marlin;
use poly_commit::ipa_pc::InnerProductArgPC;
use poly_commit::PolynomialCommitment;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};
use r1cs_crypto::FieldBasedHashGadget;
use r1cs_crypto::TweedleFrDensityOptimizedPoseidonHashGadget;
//use r1cs_crypto::TweedleFrPoseidonHashGadget;
use blake2::Blake2s;
use r1cs_std::alloc::AllocGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::nonnative::short_weierstrass::short_weierstrass_jacobian::GroupAffineNonNativeGadget;
use r1cs_std::groups::GroupGadget;
use r1cs_std::{boolean::Boolean, fields::fp::FpGadget, prelude::EqGadget, Assignment};
use rand::rngs::OsRng;
use rand::Rng;

// Basic algebraic types
type FieldElement = TweedleFr;
type FieldElementGadget = FpGadget<FieldElement>;

// Crypto primitives instantiations

//type FieldHashGadget = TweedleFrPoseidonHashGadget;
type FieldHashGadget = TweedleFrDensityOptimizedPoseidonHashGadget;

// Simulated types

type SimulatedFieldElement = ed25519Fq;
type SimulatedScalarFieldElement = ed25519Fr;
type SimulatedGroup = algebra::curves::ed25519::SWEd25519Affine;
type SimulatedCurveParameters = algebra::curves::ed25519::Ed25519Parameters;

type ECPointSimulationGadget =
    GroupAffineNonNativeGadget<SimulatedCurveParameters, FieldElement, SimulatedFieldElement>;

struct CSWPrototypeCircuit {
    secret: Vec<bool>,
    roots_check: bool,
    cum_roots: Vec<FieldElement>,
}

impl ConstraintSynthesizer<FieldElement> for CSWPrototypeCircuit {
    fn generate_constraints<CS: ConstraintSystem<FieldElement>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // Compute pk starting from the secret booleans
        let secret_g =
            Vec::<Boolean>::alloc(cs.ns(|| "alloc secret bits"), || Ok(self.secret.as_slice()))?;

        let expected_pk = ECPointSimulationGadget::mul_bits_fixed_base(
            &SimulatedGroup::prime_subgroup_generator().into_projective(),
            cs.ns(|| "G^sk"),
            secret_g.as_slice(),
        )?;

        let actual_pk =
            ECPointSimulationGadget::alloc_input(cs.ns(|| "alloc expected pk"), || {
                expected_pk.get_value().get()
            })?;

        expected_pk.enforce_equal(cs.ns(|| "expected pk == actual_pk"), &actual_pk)?;

        if self.roots_check {
            // Hash stuff toghether
            let cum_roots_g = Vec::<FieldElementGadget>::alloc(cs.ns(|| "alloc roots"), || {
                Ok(self.cum_roots.as_slice())
            })?;

            let mut cum_root_g = cum_roots_g[0].clone();

            for root_g in cum_roots_g.into_iter().skip(1) {
                cum_root_g = FieldHashGadget::enforce_hash_constant_length(
                    cs.ns(|| "enforce hashes"),
                    &[cum_root_g, root_g],
                )?;
            }

            let expected_final_cum_root = cum_root_g.clone();

            let actual_final_cum_root =
                FieldElementGadget::alloc_input(cs.ns(|| "alloc actual final cum root"), || {
                    expected_final_cum_root.get_value().get()
                })?;

            expected_final_cum_root.enforce_equal(
                cs.ns(|| "expected_cum_root == actual_cum_root"),
                &actual_final_cum_root,
            )?;
        }

        Ok(())
    }
}

type TestIPAPCDee = InnerProductArgPC<DeeAffine, Blake2s>;

#[test]
fn csw_prototype_test() {
    let rng = &mut OsRng::default();

    // Generates DLOG keys
    let segment_size = 1 << 18;
    let params = TestIPAPCDee::setup(segment_size - 1).unwrap();
    let (committer_key, _) = TestIPAPCDee::trim(&params, segment_size - 1).unwrap();

    // Generate Marlin prover and verifier key
    for i in 200..=200 {
        // Setup
        println!(
            "****************NUM ROOTS***********************: {}",
            i * 10
        );
        let mut circ = CSWPrototypeCircuit {
            secret: vec![false; SimulatedScalarFieldElement::size_in_bits()],
            roots_check: i > 0,
            cum_roots: vec![FieldElement::zero(); (i * 10) + 1],
        };

        let start = std::time::Instant::now();
        let (index_pk, index_vk) =
            Marlin::<_, TestIPAPCDee, Blake2s>::index(&committer_key, circ).unwrap();
        println!("Setup time: {:?}", start.elapsed());

        let vk_size = index_vk.serialized_size();
        println!("******************VK SIZE:****************** {}", vk_size);
        let pk_size = index_pk.serialized_size();
        println!("******************PK SIZE:****************** {}", pk_size);

        // Prove
        let mut secret = SimulatedScalarFieldElement::rand(rng).write_bits();
        secret.reverse();
        circ = CSWPrototypeCircuit {
            secret,
            roots_check: i > 0,
            cum_roots: (0..((i * 10) + 1))
                .map(|_| rng.gen())
                .collect::<Vec<FieldElement>>(),
        };

        let start = std::time::Instant::now();
        let proof = Marlin::<_, TestIPAPCDee, Blake2s>::prove(
            &index_pk,
            &committer_key,
            circ,
            true,
            Some(rng),
        )
        .unwrap();
        println!("Proof creation time: {:?}", start.elapsed());

        let proof_size = proof.serialized_size();
        println!(
            "******************PROOF SIZE:****************** {}",
            proof_size
        );

        println!(
            "******************PROOF+VK SIZE:****************** {}",
            proof_size + vk_size
        );
    }
}
