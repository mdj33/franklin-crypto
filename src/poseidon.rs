//! This is an implementation of EdDSA as refered in literature
//! Generation of randomness is not specified

use sha2::{Sha256, Digest};
use bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr, BitIterator};
use rand::{Rng};
use std::io::{self, Read, Write};
use std::convert::{TryInto, TryFrom};
use crate::pedersen_hash::*;
use jubjub::{
    FixedGenerators, 
    JubjubEngine, 
    JubjubParams, 
    Unknown,
    edwards::Point,
    ToUniform};
use hmac::{Hmac, Mac, NewMac};
use crate::rescue::{RescueEngine};

use util::{hash_to_scalar, hash_to_scalar_s, sha256_hash_to_scalar, rescue_hash_to_scalar};

use ::constants::{MATTER_EDDSA_BLAKE2S_PERSONALIZATION};

type HmacSha256 = Hmac<Sha256>;


fn h_star<E: JubjubEngine>(a: &[u8], b: &[u8]) -> E::Fs {
    hash_to_scalar::<E>(b"Zcash_RedJubjubH", a, b)
}



#[derive(Clone)]
pub struct Signature<E: JubjubEngine> {
    pub r: Point<E, Unknown>,
    pub s: E::Fs,
}

pub struct PrivateKey<E: JubjubEngine>(pub E::Fs);

#[derive(Clone)]
pub struct PublicKey<E: JubjubEngine>(pub Point<E, Unknown>);

#[derive(Clone)]
pub struct Seed<E: JubjubEngine>(pub E::Fs);

impl<E: JubjubEngine> Seed<E> {
    pub fn random_seed<R: Rng>(rng: &mut R, msg: &[u8]) -> Self {
        // T = (l_H + 128) bits of randomness
        // For H*, l_H = 512 bits
        let mut t = [0u8; 80];
        rng.fill_bytes(&mut t[..]);

        // Generate randomness using hash function based on some entropy and the message
        // Generation of randommess is completely off-chain, so we use BLAKE2b!
        // r = H*(T || M)
        Seed(h_star::<E>(&t[..], msg))
    }

}



impl<E: JubjubEngine> PrivateKey<E> {
    pub fn randomize(&self, alpha: E::Fs) -> Self {
        let mut tmp = self.0;
        tmp.add_assign(&alpha);
        PrivateKey(tmp)
    }


    pub fn sign_poseidon_message(
        &self,
        msg: &[u8],
        seed: &Seed<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> Signature<E> {
        let pk = PublicKey::from_private(&self, p_g, params);
        let order_check = pk.0.mul(E::Fs::char(), params);
        assert!(order_check.eq(&Point::zero()));

        // R = seed . P_G
        let r_g = params.generator(p_g).mul(seed.0, params);


        // pad with zeroes to match representation length
        let mut msg_padded : Vec<u8> = msg.iter().cloned().collect();
        for _ in 0..(32 - msg.len()) {
            msg_padded.extend(&[0u8;1]);
        }

        // S = seed + M . sk
        let mut s = E::Fs::to_uniform_32(msg_padded.as_ref());

        s.mul_assign(&self.0);
        s.add_assign(&seed.0);

        let as_unknown = Point::from(r_g);
        Signature { r: as_unknown, s: s }
    }


}



impl<E: JubjubEngine> PublicKey<E> {
    pub fn from_private(privkey: &PrivateKey<E>, p_g: FixedGenerators, params: &E::Params) -> Self {
        let res = params.generator(p_g).mul(privkey.0, params).into();
        PublicKey(res)
    }




    pub fn verify_for_poseidon_message(
        &self,
        msg: &[u8],
        sig: &Signature<E>,
        p_g: FixedGenerators,
        params: &E::Params,
    ) -> bool {
        // c = M

        // pad with zeroes to match representation length
        let mut msg_padded : Vec<u8> = msg.iter().cloned().collect();
        msg_padded.resize(32, 0u8);

        let c = E::Fs::to_uniform_32(msg_padded.as_ref());

        // this one is for a simple sanity check. In application purposes the pk will always be in a right group
        let order_check_pk = self.0.mul(E::Fs::char(), params);
        if !order_check_pk.eq(&Point::zero()) {
            return false;
        }

        // r is input from user, so always check it!
        let order_check_r = sig.r.mul(E::Fs::char(), params);
        if !order_check_r.eq(&Point::zero()) {
            return false;
        }

        // 0 = h_G(-S . P_G + R + c . vk)
        // self.0.mul(c, params).add(&sig.r, params).add(
        //     &params.generator(p_g).mul(sig.s, params).negate().into(),
        //     params
        // ).mul_by_cofactor(params).eq(&Point::zero());


        // 0 = -S . P_G + R + c . vk that requires all points to be in the same group
        self.0.mul(c, params).add(&sig.r, params).add(
            &params.generator(p_g).mul(sig.s, params).negate().into(),
            params
        ).eq(&Point::zero())
    }


}


#[cfg(test)]
mod baby_tests {
    use bellman::pairing::bn256::Bn256;
    use rand::{XorShiftRng, SeedableRng, thread_rng};

    use alt_babyjubjub::{AltJubjubBn256, fs::Fs, edwards, FixedGenerators};

    use super::*;


    #[test]
    fn random_seed() {
        let rng = &mut thread_rng();
        let msg = b"Foo bar";
        let seed1 = Seed::<Bn256>::random_seed(rng, msg);
        let seed2 = Seed::<Bn256>::random_seed(rng, msg);
        assert_ne!(seed1.0, seed2.0);
    }



    use poseidon_hash::bn256::Bn256PoseidonParams;
    use poseidon_hash::{poseidon_hash, StatefulSponge};
    use bellman::pairing::bn256::{ Fr};
    use poseidon_hash::PoseidonHashParams;
    pub fn fr_to_be_bytes_padding(v: &Fr) -> [u8; 32] {
        let mut result = [0u8; 32];

        let repr = v.into_repr();
        repr.write_be(result.as_mut_slice()).unwrap();
        result
    }
    #[test]
    fn random_signatures_for_poseidon_message() {
        let mut rng = XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let params = Bn256PoseidonParams::new_checked_2_into_1();
        let input: Vec<Fr> = (0..(params.rate())).map(|_| rng.gen()).collect();
        let expected = poseidon_hash::<Bn256>(&params, &input[..]);

        let rng = &mut thread_rng();
        let p_g = FixedGenerators::SpendingKeyGenerator;
        let params = &AltJubjubBn256::new();

        let sk = PrivateKey::<Bn256>(rng.gen());
        let vk = PublicKey::from_private(&sk, p_g, params);

        let a = &expected[0];
        let msg1 = &fr_to_be_bytes_padding(a);

        let max_message_size: usize = 32;

        let seed1 = Seed::random_seed(rng, msg1);

        let sig1 = sk.sign_poseidon_message(msg1, &seed1, p_g, params);
        assert!(vk.verify_for_poseidon_message(msg1, &sig1, p_g, params));
    }

}
