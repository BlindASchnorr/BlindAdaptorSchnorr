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


pub struct Signer{}

pub struct SignerState{
    pub r: BigInt
}

pub struct Signer_Output{
    pub R: Point,
    pub signer_state: SignerState
}


impl Signer {

    pub fn response_1(ciphertext: &BigInt)-> Signer_Output{
        let mut rng = rand::thread_rng();
        let mask = (BigInt::from(1) << 253) - 1;
        let Generator_jubjub = &*B8;
        let r = rng.gen_bigint(254)& &mask;
        let R = Generator_jubjub.mul_scalar(&r);
        let signer_state = SignerState{r: r};
        let signer_output = Signer_Output{R: R, signer_state: signer_state};
        signer_output

    }

    pub fn response_2(
        x: &BigInt, 
        challenge: &BigInt, 
        params: ProvingKey<Bn254>,
        //builder: CircomBuilder<Bn254>,
        inputs: Vec<Fr>,
        proof: &Proof<Bn254>, 
        r: &BigInt, 
        adaptor_witness: &BigInt
    ) -> Result<BigInt, color_eyre::Report> {
        let pvk = GrothBn::process_vk(&params.vk).unwrap();

        let verified = GrothBn::verify_with_processed_vk(&pvk, &inputs, &proof)?;

        println!("verified in signer: {:?}", verified);


        assert!(verified);
        
            let c_times_x = challenge*x;
            let r_plus_y = r+adaptor_witness;
            let s_prime = c_times_x+r_plus_y;
            //let s_prime_mod_ORDER = s_prime.mod_floor(&Q);
            Ok(s_prime)
    }
}
