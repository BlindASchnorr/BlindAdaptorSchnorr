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
pub struct Signer{}

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

        //convert ORDER
        //let order_string = ORDER.to_string(); // Make sure this gives a decimal representation
        //let order: BigInt = BigInt::from_str_radix(&order_string, 10).unwrap();
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

impl Signer {
    pub fn response(
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

#[test]
fn verify() {
    let Generator_jubjub = &*B8;
    let mut rng = rand::thread_rng();
    let mask = (BigInt::from(1) << 253) - 1;
    let adaptor_witness = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
    println!("adaptor_witness: {:?}", adaptor_witness);
    let adaptor_statement = Generator_jubjub.mul_scalar(&adaptor_witness);
    println!("adaptor_statement: {:?}", adaptor_statement);
    let r = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
    println!("r: {:?}", r);
    let R = Generator_jubjub.mul_scalar(&r);
    println!("R: {:?}", R);
    let r_plus_as = (r.clone()+adaptor_witness.clone()).mod_floor(&Q);
    println!("r_plus_as: {:?}", r_plus_as);
    let R_plus_as = Generator_jubjub.mul_scalar(&r_plus_as);
    println!("R_plus_as: {:?}", R_plus_as);
    let R_projective = R.projective();
    let m = rng.gen_bigint(10)& &mask;
    let x = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
    println!("x: {:?}", x);
    let X = Generator_jubjub.mul_scalar(&x);
    let alpha = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
    let alpha_G = Generator_jubjub.mul_scalar(&alpha);
    let alpha_G_projective = alpha_G.projective();
    let beta = (rng.gen_bigint(254)& &mask).mod_floor(&Q);
    let beta_X = X.mul_scalar(&beta.clone());
    let beta_X_projective = beta_X.projective();
    let adaptor_statement_projective = adaptor_statement.projective();
    let R_plus_as_projective = R_projective.add(&adaptor_statement_projective);
    let R_plus_as = R_plus_as_projective.affine();
    println!("R_plus_as: {:?}", R_plus_as);
    let R_prime_projective = alpha_G_projective.add(&beta_X_projective).add(&R_projective);
    let R_prime = R_prime_projective.affine();
    let hash_value = schnorr_hash(&X, m.clone(), &R_prime).expect("fail to schnorr_hash");
    let challenge = (hash_value.clone() + beta).mod_floor(&Q);
    println!("challenge: {:?}", challenge);
    let cX = X.mul_scalar(&challenge.clone());
    //let cx = (challenge.clone()*x.clone()).mod_floor(&Q);
    let cx = challenge.clone()*x.clone();
    let cx_G = Generator_jubjub.mul_scalar(&cx);
    println!("cx_G: {:?}", cx_G);
    let cX_projective = cX.projective();
    let cX = cX_projective.affine();
    println!("cX: {:?}", cX);
    let R_plus_as_plus_cX_projective = R_plus_as_projective.add(&cX_projective);
    let R_plus_as_plus_cX = R_plus_as_plus_cX_projective.affine();
    println!("R_plus_as_plus_cX: {:?}", R_plus_as_plus_cX);
    let s_prime = (r+adaptor_witness+challenge.clone()*x);
    let s_prime_G = Generator_jubjub.mul_scalar(&s_prime);
    println!("s_prime_G: {:?}", s_prime_G);
    let signature = User::verify(&s_prime, &alpha, &R, R_prime, &adaptor_statement, &challenge, &X);
}


fn main()-> Result<()> {
    let start = Instant::now();
    let cfg = CircomConfig::<Bn254>::new(
        "./src/circ.wasm",
        "./src/circ.r1cs",
    )?;
    let mut builder = CircomBuilder::new(cfg);
    let duration = start.elapsed();
    println!("Time elapsed to transform r1cs circuit is: {:?}", duration);
    let start = Instant::now();
    let Generator_jubjub = &*B8;
    let mut rng = rand::thread_rng();
    let adaptor_witness = rng.gen_bigint(254);
    let adaptor_statement = Generator_jubjub.mul_scalar(&adaptor_witness);
    let mask = (BigInt::from(1) << 253) - 1;
    let r = rng.gen_bigint(254)& &mask;
    let m = rng.gen_bigint(10)& &mask;
    let x = rng.gen_bigint(254)& &mask;
    let X = Generator_jubjub.mul_scalar(&x);
    let R = Generator_jubjub.mul_scalar(&r);
    let user_output_1 = User::sent_1(&m); 
    let alpha = user_output_1.user_state.alpha;
    let beta = user_output_1.user_state.beta;
    let rho = user_output_1.user_state.rho;
    let rho_G = user_output_1.rho_G;
    let user_output_2 = User::sent_2(&R, &X, &alpha, &beta, &rho, &rho_G, builder, &m).unwrap();
    let challenge = user_output_2.challenge;
    let inputs = user_output_2.inputs;
    let params = user_output_2.params;
    let proof = &user_output_2.proof;
    let signer_response = Signer::response(&x, &challenge, params, inputs, proof, &r, &adaptor_witness).unwrap();
    let s_prime = &signer_response;
    let R_prime = user_output_2.R_prime;
    let signature = User::verify(s_prime, &alpha, &R, R_prime, &adaptor_statement, &challenge, &X);
    let duration = start.elapsed();
    println!("Time elapsed completing blind adaptor signature is: {:?}", duration);
    Ok(())
}