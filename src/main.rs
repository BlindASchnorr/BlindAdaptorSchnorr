use std::ops::Add;
use ark_bn254::Config;
use num_integer::Integer;
use ark_circom::circom::{CircomConfig, CircomBuilder};
use babyjubjub_rs::{self, Point, schnorr_hash, B8, Q};
//use poseidon_rs::Fr;
use ark_groth16::{Groth16, Proof, ProvingKey};
use ark_bn254::{Bn254, Fr};
use ark_snark::SNARK;
use num_bigint::{BigInt, RandBigInt, ToBigInt};
use color_eyre::Result;
use rand::Rng;
use num_traits::{One,ToPrimitive,Num};
//use ark_ff::Field;
//use ff::Field as ff_field;
use ff::PrimeField;
use rand::rngs::ThreadRng;
use rand::thread_rng;
type GrothBn = Groth16<Bn254>;
use std::time::Instant;
use thiserror::Error;

mod user;
use user::{User, UserState, User_Output_1, User_Output_2, Signature};
mod signer;
use signer::Signer;


#[derive(Error, Debug)]
pub enum AppError {
    #[error("Failed to parse BigInt: {0}")]
    BigIntParseError(String),
    #[error("Signature verification failed")]
    SignatureVerificationFailed,
    #[error("Proof verification failed")]
    ProofVerificationFailed,
    #[error("Circom build error: {0}")]
    CircomBuildError(String),
    #[error("Parameters generation error: {0}")]
    ParamsGenerationError(String),
    // Add other error variants as needed
}


// #[test]
// fn verify() {
//     let Generator_jubjub = &*B8;
//     let mut rng = rand::thread_rng();
//     let mask = (BigInt::from(1) << 253) - 1;
//     let adaptor_witness = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
//     println!("adaptor_witness: {:?}", adaptor_witness);
//     let adaptor_statement = Generator_jubjub.mul_scalar(&adaptor_witness);
//     println!("adaptor_statement: {:?}", adaptor_statement);
//     let r = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
//     println!("r: {:?}", r);
//     let R = Generator_jubjub.mul_scalar(&r);
//     println!("R: {:?}", R);
//     let r_plus_as = (r.clone()+adaptor_witness.clone()).mod_floor(&Q);
//     println!("r_plus_as: {:?}", r_plus_as);
//     let R_plus_as = Generator_jubjub.mul_scalar(&r_plus_as);
//     println!("R_plus_as: {:?}", R_plus_as);
//     let R_projective = R.projective();
//     let m = rng.gen_bigint(10)& &mask;
//     let x = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
//     println!("x: {:?}", x);
//     let X = Generator_jubjub.mul_scalar(&x);
//     let alpha = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
//     let alpha_G = Generator_jubjub.mul_scalar(&alpha);
//     let alpha_G_projective = alpha_G.projective();
//     let beta = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
//     let beta_X = X.mul_scalar(&beta.clone());
//     let beta_X_projective = beta_X.projective();
//     let adaptor_statement_projective = adaptor_statement.projective();
//     let R_plus_as_projective = R_projective.add(&adaptor_statement_projective);
//     let R_plus_as = R_plus_as_projective.affine();
//     println!("R_plus_as: {:?}", R_plus_as);
//     let R_prime_projective = alpha_G_projective.add(&beta_X_projective).add(&R_projective);
//     let R_prime = R_prime_projective.affine();
//     let hash_value = schnorr_hash(&X, m.clone(), &R_prime).expect("fail to schnorr_hash");
//     let challenge = (hash_value.clone() + beta).mod_floor(&Q);
//     println!("challenge: {:?}", challenge);
//     let cX = X.mul_scalar(&challenge.clone());
//     //let cx = (challenge.clone()*x.clone()).mod_floor(&Q);
//     let cx = challenge.clone()*x.clone();
//     let cx_G = Generator_jubjub.mul_scalar(&cx);
//     println!("cx_G: {:?}", cx_G);
//     let cX_projective = cX.projective();
//     let cX = cX_projective.affine();
//     println!("cX: {:?}", cX);
//     let R_plus_as_plus_cX_projective = R_plus_as_projective.add(&cX_projective);
//     let R_plus_as_plus_cX = R_plus_as_plus_cX_projective.affine();
//     println!("R_plus_as_plus_cX: {:?}", R_plus_as_plus_cX);
//     let s_prime = (r+adaptor_witness+challenge.clone()*x);
//     let s_prime_G = Generator_jubjub.mul_scalar(&s_prime);
//     println!("s_prime_G: {:?}", s_prime_G);
//     let signature = User::verify(&s_prime, &alpha, &R, R_prime, &adaptor_statement, &challenge, &X);
// }


fn main()-> Result<()> {
    let start = Instant::now();
    //As a preprocessing, we first build the circuit
    let cfg = CircomConfig::<Bn254>::new(
        "./src/circ.wasm",
        "./src/circ.r1cs",
    )?;
    let mut builder = CircomBuilder::new(cfg);
    let duration = start.elapsed();
    println!("Time elapsed to transform r1cs circuit is: {:?}", duration);
    let start = Instant::now();
    //Then we generate the parameters
    let Generator_jubjub = &*B8;
    let mut rng = rand::thread_rng();

    //generate the secret key and public key
    let x = rng.gen_bigint(254)& &mask;
    let X = Generator_jubjub.mul_scalar(&x);

    //prepare the adaptor statement 
    let adaptor_witness = rng.gen_bigint(254);
    let adaptor_statement = Generator_jubjub.mul_scalar(&adaptor_witness);
    let mask = (BigInt::from(1) << 253) - 1;

    //message
    let m = rng.gen_bigint(10)& &mask;

    //the first step of the protocol: compute the ciphertext
    let user_output_1 = User::sent_1(&m); 

    //the second step of the protocol: compute the challenge group element
    let signer_output = signer::Signer::response_1(&user_output_1.ciphertext);
    let r = signer_output.signer_state.r;
    let R = signer_output.R;

    //the third step of the protocol: compute the proof
    let alpha = user_output_1.user_state.alpha;
    let beta = user_output_1.user_state.beta;
    let rho = user_output_1.user_state.rho;
    let rho_G = user_output_1.rho_G;
    let user_output_2 = User::sent_2(&R, &X, &alpha, &beta, &rho, &rho_G, builder, &m).unwrap();
    let challenge = user_output_2.challenge;
    let inputs = user_output_2.inputs;
    let params = user_output_2.params;
    let proof = &user_output_2.proof;

    //the fourth step of the protocol: compute the blind adaptor schnorr signature
    let signer_response = Signer::response_2(&x, &challenge, params, inputs, proof, &r, &adaptor_witness).unwrap();
    let s_prime = &signer_response;
    let R_prime = user_output_2.R_prime;

    //the fifth step of the protocol: verify and output the adaptor schnorr signature
    let signature = User::verify(s_prime, &alpha, &R, R_prime, &adaptor_statement, &challenge, &X);
    let duration = start.elapsed();
    println!("Time elapsed completing blind adaptor signature is: {:?}", duration);
    Ok(())
}