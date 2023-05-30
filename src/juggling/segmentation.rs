#![allow(non_snake_case)]
/*
centipede

Copyright 2018 by Kzen Networks

This file is part of centipede library
(https://github.com/KZen-networks/centipede)

Escrow-recovery is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public
License as published by the Free Software Foundation, either
version 3 of the License, or (at your option) any later version.

@license GPL-3.0+ <https://github.com/KZen-networks/centipede/blob/master/LICENSE>
*/

const SECRETBITS: usize = 256;

use std::marker::PhantomData;
use std::ops::{Mul, Shl, Shr};

use curv::arithmetic::traits::*;
use curv::elliptic::curves::traits::*;
use curv::BigInt;
use juggling::proof_system::{Helgamal, Helgamalsegmented, Witness};
#[cfg(feature = "parallel")]
use rayon::iter::IntoParallelIterator;
#[cfg(feature = "parallel")]
use rayon::iter::ParallelIterator;

use Errors::{self, ErrorDecrypting};

pub struct Msegmentation<GE>(PhantomData<GE>);

impl<GE> Msegmentation<GE>
where
    GE: ECPoint + Clone + Copy + Sync + Send + for<'a> Mul<&'a GE::Scalar, Output=GE>,
    GE::Scalar: ECScalar + Clone + Copy + Sync + Send
    + PartialEq<GE::Scalar> + for<'a> Mul<&'a GE::Scalar, Output=GE::Scalar>,
{
    pub fn get_segment_k(secret: &GE::Scalar, segment_size: &usize, k: u8) -> GE::Scalar {
        let ss_bn = secret.to_big_int();
        let segment_size_u32 = segment_size.clone() as u32;
        let msb = segment_size_u32 * (k as u32 + 1);
        let lsb = segment_size_u32 * k as u32;
        let two_bn = BigInt::from(2);
        let max = BigInt::pow(&two_bn, msb) - BigInt::from(1);
        let min = BigInt::pow(&two_bn, lsb) - BigInt::from(1);
        let mask = max - min;
        let segment_k_bn = mask & ss_bn;
        let segment_k_bn_rotated =
            BigInt::shr(segment_k_bn, (k * segment_size.clone() as u8) as usize);
        // println!("test = {:?}", test.to_str_radix(16));
        if segment_k_bn_rotated == BigInt::zero() {
            ECScalar::zero()
        } else {
            ECScalar::from(&segment_k_bn_rotated)
        }
    }
    //returns r_k,{D_k,E_k}
    pub fn encrypt_segment_k(
        secret: &GE::Scalar,
        random: &GE::Scalar,
        segment_size: &usize,
        k: u8,
        pub_ke_y: &GE,
        G: &GE,
    ) -> Helgamal<GE> {
        let segment_k = Msegmentation::<GE>::get_segment_k(secret, segment_size, k);
        let E_k = *G * random;
        let r_kY = *pub_ke_y * random;
        if segment_k == GE::Scalar::zero() {
            let D_k = r_kY;
            Helgamal { D: D_k, E: E_k }
        } else {
            let x_kG = *G * &segment_k;
            let D_k = r_kY + x_kG;
            Helgamal { D: D_k, E: E_k }
        }
    }

    // TODO: find a way using generics to combine the following two fn's
    pub fn assemble_fe(segments: &Vec<GE::Scalar>, segment_size: &usize) -> GE::Scalar {
        let two = BigInt::from(2);
        let mut segments_2n = segments.clone();
        let seg1 = segments_2n.remove(0);
        let seg_sum = segments_2n
            .iter()
            .zip(0..segments_2n.len())
            .fold(seg1, |acc, x| {
                if GE::Scalar::zero() == x.0.clone() {
                    acc
                } else {
                    let two_to_the_n = two.pow(segment_size.clone() as u32);
                    let two_to_the_n_shifted = two_to_the_n.shl(x.1 * segment_size);
                    let two_to_the_n_shifted_fe: GE::Scalar = ECScalar::from(&two_to_the_n_shifted);
                    let shifted_segment = two_to_the_n_shifted_fe * x.0.clone();
                    acc + shifted_segment
                }
            });
        return seg_sum;
    }

    pub fn assemble_ge(segments: &Vec<GE>, segment_size: &usize) -> GE {
        let two = BigInt::from(2);
        let mut segments_2n = segments.clone();
        let seg1 = segments_2n.remove(0);
        let seg_sum = segments_2n
            .iter()
            .zip(0..segments_2n.len())
            .fold(seg1, |acc, x| {
                let two_to_the_n = two.pow(segment_size.clone() as u32);
                let two_to_the_n_shifted = two_to_the_n.shl(x.1 * segment_size);
                let two_to_the_n_shifted_fe: GE::Scalar = ECScalar::from(&two_to_the_n_shifted);
                let shifted_segment = x.0.clone() * two_to_the_n_shifted_fe;
                acc + shifted_segment
            });
        return seg_sum;
    }

    pub fn to_encrypted_segments(
        secret: &GE::Scalar,
        segment_size: &usize,
        num_of_segments: usize,
        pub_ke_y: &GE,
        G: &GE,
    ) -> (Witness<GE::Scalar>, Helgamalsegmented<GE>) {
        assert_eq!(*segment_size * num_of_segments, SECRETBITS);
        let r_vec = (0..num_of_segments)
            .map(|_| ECScalar::new_random())
            .collect::<Vec<GE::Scalar>>();
        #[cfg(feature = "parallel")]
        let iter = (0..num_of_segments).into_par_iter();
        #[cfg(not(feature = "parallel"))]
        let iter = (0..num_of_segments).into_iter();
        let segmented_enc = iter
            .map(|i| {
                //  let segment_i = mSegmentation::get_segment_k(secret,segment_size,i as u8);
                Msegmentation::<GE>::encrypt_segment_k(
                    secret,
                    &r_vec[i],
                    &segment_size,
                    i as u8,
                    pub_ke_y,
                    G,
                )
            })
            .collect::<Vec<Helgamal<GE>>>();
        let x_vec = (0..num_of_segments)
            .map(|i| Msegmentation::<GE>::get_segment_k(secret, segment_size, i as u8))
            .collect::<Vec<GE::Scalar>>();
        let w = Witness { x_vec, r_vec };
        let heg_segmented = Helgamalsegmented { DE: segmented_enc };
        (w, heg_segmented)
    }

    //TODO: implement a more advance algorithm for dlog
    pub fn decrypt_segment(
        DE: &Helgamal<GE>,
        G: &GE,
        private_key: &GE::Scalar,
        limit: &u32,
        table: &[GE],
    ) -> Result<GE::Scalar, Errors> {
        let mut result = None;

        let limit_plus_one = limit.clone() + 1u32;
        let out_of_limit_fe: GE::Scalar = ECScalar::from(&BigInt::from(limit_plus_one));
        let out_of_limit_ge: GE = G.clone() * &out_of_limit_fe;
        let yE = DE.E.clone() * private_key;
        // handling 0 segment
        let mut D_minus_yE: GE = out_of_limit_ge;
        if yE == DE.D.clone() {
            result = Some(());
        } else {
            D_minus_yE = DE.D.sub_point(&yE.get_element());
        }
        // TODO: make bound bigger then 32
        let mut table_iter = table.iter().enumerate();
        // find is short-circuting //TODO: counter measure against side channel attacks
        let matched_value_index = table_iter.find(|&x| x.1 == &D_minus_yE);
        match matched_value_index {
            Some(x) => Ok(ECScalar::from(&BigInt::from(x.0 as u32 + 1))),
            None => {
                return if result.is_some() {
                    Ok(ECScalar::zero())
                } else {
                    Err(ErrorDecrypting)
                };
            }
        }
    }

    pub fn decrypt(
        DE_vec: &Helgamalsegmented<GE>,
        G: &GE,
        private_key: &GE::Scalar,
        segment_size: &usize,
    ) -> Result<GE::Scalar, Errors> {
        let limit = 2u32.pow(segment_size.clone() as u32);
        #[cfg(feature = "parallel")]
        let iter = (1..limit).into_par_iter();
        #[cfg(not(feature = "parallel"))]
        let iter = (1..limit).into_iter();
        let test_ge_table = iter
            .map(|i| {
                let test_fe = ECScalar::from(&BigInt::from(i));
                *G * &test_fe
            })
            .collect::<Vec<GE>>();
        #[cfg(feature = "parallel")]
        let iter = (0..DE_vec.DE.len()).into_par_iter();
        #[cfg(not(feature = "parallel"))]
        let iter = (0..DE_vec.DE.len()).into_iter();
        let vec_secret = iter
            .map(|i| {
                let result = Msegmentation::<GE>::decrypt_segment(
                    &DE_vec.DE[i],
                    G,
                    private_key,
                    &limit,
                    &test_ge_table,
                );
                //   .expect("error decrypting");
                result
            })
            .collect::<Vec<Result<GE::Scalar, Errors>>>();
        let mut flag = true;
        let vec_secret_unwrap = (0..vec_secret.len())
            .into_iter()
            .map(|i| {
                if vec_secret[i].is_err() {
                    flag = false;
                    GE::Scalar::zero()
                } else {
                    vec_secret[i].unwrap()
                }
            })
            .collect::<Vec<GE::Scalar>>();
        match flag {
            false => Err(ErrorDecrypting),
            true => Ok(Msegmentation::<GE>::assemble_fe(
                &vec_secret_unwrap,
                &segment_size,
            )),
        }
    }
}
