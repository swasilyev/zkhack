use std::borrow::Borrow;
use std::marker::PhantomData;
use std::ops::AddAssign;

use ark_bls12_381::Bls12_381;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::bls12::Bls12Config;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, Fp, Zero};
use ark_ff::PrimeField;
use ark_groth16::PreparedVerifyingKey;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::nonnative::{AllocatedNonNativeFieldVar, NonNativeFieldVar};
use ark_r1cs_std::fields::nonnative::params::OptimizationType;
use ark_r1cs_std::groups::curves::short_weierstrass::AffineVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{test_rng, UniformRand};

#[derive(Clone)]
struct Point<NF: PrimeField, F: FieldVar<FF, NF>> {
    f: PhantomData<NF>,
    x: F,
    y: F,
}

impl<NF: PrimeField, F: FieldVar<FF, NF>> Point<NF, F> {
    fn add(&self, other: &Self) -> Result<Self, SynthesisError> {
        let x1 = self.x.clone();
        let y1 = self.y.clone();
        let x2 = other.x.clone();
        let y2 = other.y.clone();
        let mut lambda_nominator = y2;
        lambda_nominator -= &y1;
        let mut lambda_denominator = x2.clone();
        lambda_denominator -= &x1;
        lambda_nominator *= lambda_denominator.inverse().unwrap();
        let lambda = lambda_nominator;
        let mut x = lambda.clone();
        x *= &lambda;
        x -= &x1;
        x -= &x2;
        let mut y = x1.clone();
        y -= &x;
        y *= &lambda;
        y -= &y1;
        // let lambda = &(y2 - y1) * &(x2 - x1).inverse().unwrap();
        // let x = &(&lambda * &lambda) - &(x1 + x2);
        // let y = &(&lambda * &(x1 - &x)) - y1;
        Ok(Self { f: Default::default(), x, y })
    }
}

impl<NF: PrimeField, F: FieldVar<FF, NF>> CondSelectGadget<NF> for Point<NF, F>
{
    fn conditionally_select(cond: &Boolean<NF>, true_value: &Self, false_value: &Self) -> Result<Self, SynthesisError> {
        let x = F::conditionally_select(
            cond,
            &true_value.x,
            &false_value.x,
        )?;
        let y = F::conditionally_select(
            cond,
            &true_value.y,
            &false_value.y,
        )?;

        Ok(Self { f: Default::default(), x, y })
    }
}

impl<NF: PrimeField, F: FieldVar<FF, NF>> AllocVar<ark_bls12_381::G1Affine, NF> for Point<NF, F>
{
    fn new_variable<T: Borrow<ark_bls12_381::G1Affine>>(
        cs: impl Into<Namespace<NF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let point = f().unwrap();
        let point = point.borrow();

        let x = F::new_variable(ns!(cs, "x"), || Ok(point.x().unwrap()), mode).unwrap();
        let y = F::new_variable(ns!(cs, "y"), || Ok(point.y().unwrap()), mode).unwrap();
        Ok(Self { f: Default::default(), x, y })
    }
}

type FF = ark_bls12_381::Fq;

#[derive(Default, Clone)]
pub struct ApkCircuit<NF: PrimeField, F: FieldVar<FF, NF>> {
    f: PhantomData<F>,
    keys: Vec<ark_bls12_381::G1Affine>,
    seed: ark_bls12_381::G1Affine,
    bitmask_packed: NF,
}

impl<NF: PrimeField, F: FieldVar<FF, NF>> ApkCircuit<NF, F> {
    fn new(keys: Vec<ark_bls12_381::G1Affine>, bitmask_packed: NF, seed: ark_bls12_381::G1Affine) -> Self {
        Self {
            f: Default::default(),
            keys,
            seed,
            bitmask_packed,
        }
    }
}

impl<NF: PrimeField, F: FieldVar<FF, NF>> ConstraintSynthesizer<NF> for ApkCircuit<NF, F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<NF>) -> Result<(), SynthesisError> {
        let seed = Point::<NF, F>::new_witness(cs.clone(), || Ok(self.seed)).unwrap();
        let keys: Vec<_> = self.keys.iter().map(|p| Point::new_input(cs.clone(), || Ok(p)).unwrap()).collect();
        // let mut bitmask: Vec<_> = self.bitmask.iter().map(|b| Boolean::new_witness(cs.clone(), || Ok(b)).unwrap()).collect();

        let packed = FpVar::new_input(cs.clone(), || Ok(self.bitmask_packed)).unwrap();
        let bitmask = packed.to_bits_le().unwrap();

        let n = self.keys.len();

        let mut res = seed;

        for i in 0..n {
            let new_res = res.clone().add(&keys[i])?;
            res = Point::conditionally_select(
                &bitmask[i],
                &new_res,
                &res,
            )?;
        }

        let x = F::new_input(cs.clone(), || res.x.value());
        let y = F::new_input(cs.clone(), || res.y.value());

        res.x.enforce_equal(&x.unwrap())?;
        res.y.enforce_equal(&y.unwrap())?;

        println!("{}", cs.num_constraints());

        Result::Ok(())
    }
}

pub fn point_to_scalar_nn(key: ark_bls12_381::G1Affine) -> Vec<ark_bls12_381::Fr> {
    keys_to_scalars_nn(&[key])
}

pub fn keys_to_scalars_nn(keyset: &[ark_bls12_381::G1Affine]) -> Vec<ark_bls12_381::Fr> {
    keys_to_scalars(keyset).iter()
        .flat_map(|x| AllocatedNonNativeFieldVar::get_limbs_representations(x, OptimizationType::Constraints).unwrap())
        .collect()
}

pub fn keys_to_scalars(keyset: &[ark_bls12_381::G1Affine]) -> Vec<ark_bls12_381::Fq> {
    keyset.iter().flat_map(|p| vec![p.x, p.y]).collect()
}


pub fn precommit_to_keyset<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    keys_as_scalars: &[E::ScalarField],
) -> E::G1 {
    let mut g_ic = pvk.vk.gamma_abc_g1[0].into_group();
    for (i, b) in keys_as_scalars.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul_bigint(i.into_bigint()));
    }
    g_ic
}

#[cfg(test)]
mod tests {
    use ark_bw6_767::BW6_767;
    use ark_ff::BitIteratorLE;
    use ark_groth16::{Groth16, prepare_verifying_key};
    use ark_r1cs_std::fields::nonnative::AllocatedNonNativeFieldVar;
    use ark_r1cs_std::fields::nonnative::params::OptimizationType;
    use ark_r1cs_std::ToConstraintFieldGadget;
    use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
    use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_std::{end_timer, start_timer};
    use ark_std::rand::RngCore;
    use ark_std::rand::SeedableRng;

    use crate::ApkCircuit;

    use super::*;

    #[test]
    fn test() {


        let rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

        let n = 4;
        let keys: Vec<_> = (0..n).map(|_| ark_bls12_381::G1Affine::rand(rng)).collect();
        let bitmask: Vec<_> = (0..n).map(|_| bool::rand(rng)).collect();

        let bitmask_packed = bitmask.iter().rev().fold(0u64, |acc, next_bit| (acc << 1) ^ (*next_bit as u64));


        let seed = ark_bls12_381::G1Affine::rand(rng); // TODO: shoulkd be out of g1

        let apk: ark_bls12_381::G1Projective = keys.iter().zip(bitmask.iter())
            .filter(|(_, b)| **b)
            .map(|(p, _)| p.into_group())
            .sum();
        let res: ark_bls12_381::G1Projective = seed + apk;
        let res = res.into_affine();

        {
            type NF = ark_bls12_381::Fr;

            let bitmask_packed = NF::from(bitmask_packed);

            let circuit = ApkCircuit::<NF, NonNativeFieldVar<FF, NF>>::new(keys.clone(), bitmask_packed, seed);
            let (pk, vk) = Groth16::<Bls12_381>::setup(circuit.clone(), rng).unwrap();
            let pvk = prepare_verifying_key(&vk);

            let keyset_inputs = keys_to_scalars_nn(&keys);
            let keyset_commitment = precommit_to_keyset(&pvk, &keyset_inputs);

            let t_proof = start_timer!(|| "proof");
            let proof = Groth16::<Bls12_381>::prove(&pk, circuit.clone(), rng).unwrap();
            end_timer!(t_proof);

            let mut public_inputs = vec![bitmask_packed];
            public_inputs.extend(point_to_scalar_nn(res));

            let mut prepared_inputs = keyset_commitment;
            for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1 + keyset_inputs.len())) {
                prepared_inputs.add_assign(&b.mul_bigint(i.into_bigint()));
            }

            assert!(Groth16::<Bls12_381>::verify_proof_with_prepared_inputs(&pvk, &proof, &prepared_inputs).unwrap());
        }

        // {
        //     type NF = FF;
        //
        //     let bitmask_packed = NF::from(bitmask_packed);
        //
        //     let circuit = ApkCircuit::<NF, FpVar<NF>>::new(keys.clone(), bitmask_packed, seed);
        //     let (pk, vk) = Groth16::<BW6_767>::setup(circuit.clone(), rng).unwrap();
        //     let pvk = prepare_verifying_key(&vk);
        //
        //     let keyset_inputs = keys_to_scalars_nn(&keys);
        //     let keyset_commitment = precommit_to_keyset(&pvk, &keyset_inputs);
        //
        //     let t_proof = start_timer!(|| "proof");
        //     let proof = Groth16::<BW6_767>::prove(&pk, circuit.clone(), rng).unwrap();
        //     end_timer!(t_proof);
        //
        //     let mut public_inputs = vec![bitmask_packed];
        //     public_inputs.extend(keys_to_scalars(&[res]));
        //
        //     let mut prepared_inputs = keyset_commitment;
        //     for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1 + keyset_inputs.len())) {
        //         prepared_inputs.add_assign(&b.mul_bigint(i.into_bigint()));
        //     }
        //
        //     assert!(Groth16::<BW6_767>::verify_proof_with_prepared_inputs(&pvk, &proof, &prepared_inputs).unwrap());
        // }
    }
}