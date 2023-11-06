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

pub struct User{}

pub struct UserState{
    pub alpha: BigInt,
    pub beta: BigInt,
    pub rho: BigInt
}
pub struct User_Output_1{
    pub ciphertext: BigInt,
    pub rho_G: Point,
    pub user_state: UserState
}

pub struct User_Output_2{
    pub challenge: BigInt,
    pub proof: Proof<Bn254>,
    pub R_prime: Point,
    pub params: ProvingKey<Bn254>,
    pub inputs: Vec<Fr>
}

pub struct  Signature{
    pub R_prime: Point,
    pub s: BigInt
}

impl User {
    pub fn sent_1(m: &BigInt)->User_Output_1{
        let mut rng = thread_rng();
        let mask = (BigInt::from(1) << 253) - 1;
        let alpha = rng.gen_bigint(254)& &mask;
        let beta = rng.gen_bigint(254)& &mask;
        let rho = rng.gen_bigint(254)& &mask;
        let rho_G = B8.mul_scalar(&rho);
    
        // Calculate ciphertext = (m + rho) mod ORDER
        let ciphertext = (m + &rho).mod_floor(&Q);

        //ciphertext.add_assign(&rho);
        let user_state = UserState{alpha, beta, rho};
        User_Output_1{ciphertext, rho_G, user_state}
    }

    pub fn sent_2(R: &Point, X: &Point, alpha: &BigInt, beta: &BigInt, rho: &BigInt, rho_G: &Point, mut builder: CircomBuilder<Bn254>, m: &BigInt)-> Result<User_Output_2, color_eyre::Report>
    {
        let Generator_jubjub = &*B8;
        let alpha_G = Generator_jubjub.mul_scalar(&alpha);
        let alpha_G_projective = alpha_G.projective();
        let beta_X = X.mul_scalar(beta);
        let beta_X_projective = beta_X.projective();
        let R_projective = R.projective();
        let R_prime_projective = alpha_G_projective.add(&beta_X_projective).add(&R_projective);
        let R_prime = R_prime_projective.affine();


        //hash R', X, m
        let hash_value = schnorr_hash(&X, m.clone(), &R_prime).expect("fail to schnorr_hash");


        let c = (hash_value.clone() + beta).mod_floor(&Q);

    
        let ciphertext = (m.clone() + rho.clone()).mod_floor(&Q);
        println!("ciphertext: {:?}", ciphertext);


        //compute input for circom
        let X_x_bigint = X.x_to_bigint();
        let X_y_bigint = X.y_to_bigint();
        let R_x_bigint = R.x_to_bigint();
        let R_y_bigint = R.y_to_bigint();
        let rho_G_x_bigint = rho_G.x_to_bigint();
        let rho_G_y_bigint = rho_G.y_to_bigint();

        // create an empty instance for setting it up
        let circom = builder.setup();

        builder.push_input("x1", X_x_bigint);
        builder.push_input("x2", X_y_bigint);
        builder.push_input("m", m.clone());
        builder.push_input("r1", R_x_bigint);
        builder.push_input("r2", R_y_bigint);
        builder.push_input("rho1", rho_G_x_bigint);
        builder.push_input("rho2", rho_G_y_bigint);
        builder.push_input("alpha", alpha.clone());
        builder.push_input("beta", beta.clone());
        builder.push_input("rho", rho.clone());
        builder.push_input("c", c.clone());
        builder.push_input("ciphertext", ciphertext.clone());

        let mut rng = thread_rng();
        let params = GrothBn::generate_random_parameters_with_reduction(circom, &mut rng)
    .map_err(|e| AppError::ParamsGenerationError(e.to_string()))?;

        let circom = builder.build().map_err(|e| {
            println!("buildError: {}", e);
            AppError::CircomBuildError(e.to_string())  
          })?;
        let inputs = circom.get_public_inputs().unwrap();

        let proof = GrothBn::prove(&params, circom, &mut rng)?;

        let pvk = GrothBn::process_vk(&params.vk).unwrap();

        let verified = GrothBn::verify_with_processed_vk(&pvk, &inputs, &proof)?;

        println!("verified in sent_2: {:?}", verified);


        //assert!(verified);
        
        Ok(User_Output_2 {
            challenge: c,
            proof,
            R_prime,
            params,
            inputs
        })

    }

    pub fn verify(s_prime: &BigInt, alpha: &BigInt, R: &Point, R_prime: Point, adaptor_statement: &Point, c: &BigInt, X: &Point)-> Result<Signature,color_eyre::Report> {

        let R_projective = R.projective();
        let adaptor_statement_projective = adaptor_statement.projective();
        let R_plus_as_projective = R_projective.add(&adaptor_statement_projective);
        let cX = X.mul_scalar(c);
        let cX_projective = cX.projective();
        let R_plus_as_plus_cX_projective = R_plus_as_projective.add(&cX_projective);
        let R_plus_as_plus_cX = R_plus_as_plus_cX_projective.affine();
        let Generator_jubjub = &*B8;
        let sG = Generator_jubjub.mul_scalar(s_prime);
        let verified = R_plus_as_plus_cX.equals(sG);
        if verified {
            let s = s_prime + alpha;
            Ok(Signature {
                R_prime, s
            })
        }
        else {
            Err(color_eyre::eyre::eyre!("signature verification failed"))
        }
    }
}
