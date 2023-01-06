/***********
 * This module implements the KOS Oblivious Transfer Extension Protocol,
 * as described in the paper "Actively Secure OT Extension with Optimal Overhead"
 * by Keller, Orsini, and Scholl (https://eprint.iacr.org/2015/546)
 *
 * Base OTs for this protocol are provided by the VSOT protocol in rot.rs
 ***********/

use std::cmp::min;
use std::io::BufWriter;
use std::result::Result;

use rand::Rng;

use bit_reverse::ParallelReverse;

use crate::utils::Curve;
use crate::utils::Scalar;

use super::ro::*;
use super::rot::*;
use super::*;
use std::error::Error;

/* Notes:
OT Extensions and transmissions are numbered by a parameter instead of a counter in the object
so that we can reuse the extension object in multiple threads and still ensure deterministic
numbering
*/

// move diagonals
// 11-12-13-14-15-16-17-18 21-22-23-24-25-26-27-28 31-32-33-34-35-36-37-38 41-42-43-44-45-46-47-48 51-52-53-54-55-56-57-58
// 11                         22                         33                         44                         55
//                         12                         23                         34
// ... to get
// 11-21-31-41-51-61-71-81 12-22-32-42-52-62-72-82 13-23-33-43-53-63-73-83
fn transpose8x8(w: u64) -> u64 {
    (w & 0x8040201008040201)
        | ((w & 0x4020100804020100) >> 7)
        | ((w & 0x2010080402010000) >> 14)
        | ((w & 0x1008040201000000) >> 21)
        | ((w & 0x0804020100000000) >> 28)
        | ((w & 0x0402010000000000) >> 35)
        | ((w & 0x0201000000000000) >> 42)
        | ((w & 0x0100000000000000) >> 49)
        | ((w & 0x0080402010080402) << 7)
        | ((w & 0x0000804020100804) << 14)
        | ((w & 0x0000008040201008) << 21)
        | ((w & 0x0000000080402010) << 28)
        | ((w & 0x0000000000804020) << 35)
        | ((w & 0x0000000000008040) << 42)
        | ((w & 0x0000000000000080) << 49)
}

//assumes rows and columns are both multiples of 8
fn transpose(data: &Vec<u8>, majtilelen: usize) -> Vec<u8> {
    let minlen = data.len() / majtilelen;
    let mintilelen = minlen / 8;
    let mut result: Vec<u8> = vec![0u8; data.len()];
    for jj in 0..mintilelen {
        for ii in 0..majtilelen {
            let chunk: u64 = ((data[(jj * 8 + 0) * majtilelen + ii] as u64) << 56)
                | ((data[(jj * 8 + 1) * majtilelen + ii] as u64) << 48)
                | ((data[(jj * 8 + 2) * majtilelen + ii] as u64) << 40)
                | ((data[(jj * 8 + 3) * majtilelen + ii] as u64) << 32)
                | ((data[(jj * 8 + 4) * majtilelen + ii] as u64) << 24)
                | ((data[(jj * 8 + 5) * majtilelen + ii] as u64) << 16)
                | ((data[(jj * 8 + 6) * majtilelen + ii] as u64) << 8)
                | ((data[(jj * 8 + 7) * majtilelen + ii] as u64) << 0);
            let transchunk: u64 = transpose8x8(chunk).swap_bits();
            result[(ii * 8 + 0) * mintilelen + jj] = ((transchunk >> 56) & 0xFF) as u8;
            result[(ii * 8 + 1) * mintilelen + jj] = ((transchunk >> 48) & 0xFF) as u8;
            result[(ii * 8 + 2) * mintilelen + jj] = ((transchunk >> 40) & 0xFF) as u8;
            result[(ii * 8 + 3) * mintilelen + jj] = ((transchunk >> 32) & 0xFF) as u8;
            result[(ii * 8 + 4) * mintilelen + jj] = ((transchunk >> 24) & 0xFF) as u8;
            result[(ii * 8 + 5) * mintilelen + jj] = ((transchunk >> 16) & 0xFF) as u8;
            result[(ii * 8 + 6) * mintilelen + jj] = ((transchunk >> 8) & 0xFF) as u8;
            result[(ii * 8 + 7) * mintilelen + jj] = ((transchunk >> 0) & 0xFF) as u8;
        }
    }
    result
}

//#[derive(Clone)]
pub struct OTESender {
    correlation: Vec<bool>,
    compressed_correlation: Vec<u8>,
    seeds: Vec<Vec<u8>>,
    curve: &'static Curve,
}

//#[derive(Clone)]
pub struct OTERecver {
    seeds: Vec<(Vec<u8>, Vec<u8>)>,
    curve: &'static Curve,
}

//#[derive(Clone)]
pub enum OTEPlayer {
    Sender(OTESender),
    Recver(OTERecver),
    Null,
}

impl OTESender {
    pub fn new<T1: Read, T2: Write, R: Rng>(
        curve: &'static Curve,
        ro: &DyadicROTagger,
		rng: &mut R,
        recv: &mut T1,
        send: &mut T2,
    ) -> Result<Self, Box<dyn Error>> {
        let fr_bits = curve.fr_bits;
        let fr_bytes = curve.fr_bytes;
        let mut correlation = vec![false; fr_bits];
        for ii in 0..fr_bits {
            correlation[ii] = (rng.next_u32() % 2) > 0;
        }

        let mut compressed_correlation = vec![0u8; fr_bytes];
        for ii in 0..fr_bytes {
            compressed_correlation[ii] = ((correlation[ii * 8 + 0] as u8) << 0)
                | ((correlation[ii * 8 + 1] as u8) << 1)
                | ((correlation[ii * 8 + 2] as u8) << 2)
                | ((correlation[ii * 8 + 3] as u8) << 3)
                | ((correlation[ii * 8 + 4] as u8) << 4)
                | ((correlation[ii * 8 + 5] as u8) << 5)
                | ((correlation[ii * 8 + 6] as u8) << 6)
                | ((correlation[ii * 8 + 7] as u8) << 7);
        }

        let seeds = rot_recv_batch(curve, &correlation, &ro, rng, recv, send)?;

        Ok(OTESender {
            correlation: correlation,
            compressed_correlation,
            seeds: seeds,
            curve,
        })
    }

    pub fn apply_refresh(
        &mut self,
        rand: &[u8],
        ro: &DyadicROTagger,
    ) -> Result<(), Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        assert!(rand.len() >= HASH_SIZE);
        let mut expanded_rand = vec![0u8; 2 * HASH_SIZE * fr_bits + fr_bits / 8];
        for ii in 0..((expanded_rand.len() + HASH_SIZE - 1) / HASH_SIZE) {
            let offset = ii * HASH_SIZE;
            let remain = min(expanded_rand.len() - offset, HASH_SIZE);
            expanded_rand[offset..(offset + remain)]
                .copy_from_slice(&hash(&[ro.next_dyadic_tag(), rand.to_vec()].concat())[0..remain]);
        }

        for ii in 0..fr_bits {
            self.correlation[ii] ^=
                ((expanded_rand[2 * HASH_SIZE * fr_bits + ii / 8] >> (ii % 8)) & 1) > 0;
            for jj in 0..HASH_SIZE {
                self.seeds[ii][jj] ^= expanded_rand
                    [((self.correlation[ii] as usize) * HASH_SIZE * fr_bits) + ii * HASH_SIZE + jj];
            }
        }
        for ii in 0..fr_bytes {
            self.compressed_correlation[ii] ^= expanded_rand[2 * HASH_SIZE * fr_bits + ii];
        }
        return Ok(());
    }

    pub fn extend<T: Read>(
        &self,
        input_len: usize,
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> Result<Vec<u8>, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        let prgoutputlen = input_len + OT_SEC_PARAM;
        let mut expanded_seeds: Vec<u8> = Vec::with_capacity(fr_bytes * prgoutputlen);
        let prgiterations = ((prgoutputlen / 8) + HASH_SIZE - 1) / HASH_SIZE;

        debug_assert!((fr_bytes * prgoutputlen) % HASH_SIZE == 0);

        let mut tagrange =
            ro.allocate_dyadic_range((fr_bits * prgiterations + prgoutputlen + 1) as u64);

        let mut prgoutput = vec![];
        for ii in 0..fr_bits {
            for jj in 0..prgiterations {
				let mut v = [tagrange.next()?, self.seeds[ii].clone()].concat();
				v.resize(HASH_BLOCK_SIZE, 0);
				prgoutput.extend_from_slice(
					&hash(&v)
				);
            }
        }

        for ii in 0..fr_bits {
            expanded_seeds.extend_from_slice(
                &prgoutput[(ii * prgiterations * HASH_SIZE)
                    ..(ii * prgiterations * HASH_SIZE + prgoutputlen / 8)],
            );
        }

        let mut seeds_combined = vec![0u8; fr_bytes * prgoutputlen + RO_TAG_SIZE];
        let mut sampled_bits = vec![0u8; fr_bytes];
        let mut sampled_seeds = vec![0u8; fr_bytes];
        recv.read_exact(&mut seeds_combined[0..fr_bytes * prgoutputlen])?;
        recv.read_exact(&mut sampled_bits)?;
        recv.read_exact(&mut sampled_seeds)?;

        seeds_combined[(fr_bytes * prgoutputlen)..].copy_from_slice(&tagrange.next()?[..]);
        let seeds_shortened = hash(&seeds_combined);

        let mut random_samples = vec![];
        for _ in 0..prgoutputlen {
            // Map for ii: [ 20B: RO tag | 32B: seeds_shortened ], total: 52B
			let mut v = [tagrange.next()?, seeds_shortened.clone()].concat();
			v.resize(HASH_BLOCK_SIZE, 0);
			random_samples.extend_from_slice(&hash(&v));
        }

        let mut check_vec: Vec<u8> = Vec::with_capacity(fr_bits * prgoutputlen / 8);
        for ii in 0..fr_bits {
            for jj in 0..(prgoutputlen / 8) {
                check_vec.push(
                    expanded_seeds[ii * (prgoutputlen / 8) + jj]
                        ^ ((self.correlation[ii] as u8)
                            * seeds_combined[ii * (prgoutputlen / 8) + jj]),
                );
            }
        }

        let transposed_check_vec = transpose(&check_vec, prgoutputlen / 8);

        let mut sampled_check = vec![0u8; fr_bytes];
        for ii in 0..prgoutputlen {
            for jj in 0..fr_bytes {
                sampled_check[jj] ^=
                    transposed_check_vec[ii * fr_bytes + jj] & random_samples[ii * fr_bytes + jj];
            }
        }

        let mut rhs = vec![0u8; fr_bytes];
        for ii in 0..fr_bytes {
            rhs[ii] = sampled_seeds[ii] ^ (self.compressed_correlation[ii] & sampled_bits[ii]);
        }

        assert_eq!(sampled_check, rhs);
        Ok(transposed_check_vec)
    }

    pub fn transfer<T: Write, R: Rng>(
        &self,
        input_len: &[usize],
        input_correlation: &[&Scalar],
        transposed_seed: &[Vec<u8>],
        ro: &DyadicROTagger,
		rng: &mut R,
        send: &mut T,
    ) -> Result<Vec<Vec<Scalar>>, Box<dyn Error>> {
        let fr_bytes = self.curve.fr_bytes;
        let input_count: usize = input_len.len();
        let total_input_len: usize = input_len.iter().sum();
        let mut tagrange =
            ro.allocate_dyadic_range((2 * total_input_len + 2 * input_count + 2) as u64);

        let mut hasherinput = transposed_seed
            .iter()
            .flat_map(|seed| seed.chunks(HASH_SIZE))
            .flat_map(|seed| {
                let tag = tagrange.next().unwrap();
                [
                    tag.clone(),
                    seed.to_vec(),
                    vec![0; HASH_BLOCK_SIZE - HASH_SIZE - RO_TAG_SIZE],
                    tag,
                    seed.iter()
                        .zip(&self.compressed_correlation)
                        .map(|(a, b)| a ^ b)
                        .collect(),
                    vec![0; HASH_BLOCK_SIZE - HASH_SIZE - RO_TAG_SIZE],
                ]
                .concat()
            })
            .collect::<Vec<_>>();
        let mut vals0 = Vec::with_capacity(input_count);
        let mut check_vals0 = Vec::with_capacity(input_count);
        let check_alpha = (0..input_count)
            .map(|_| self.curve.rand_scalar(rng))
            .collect::<Vec<_>>();

        let hashoutput = hash_multi(&hasherinput).concat();

        let mut correction_vec_raw = vec![0u8; total_input_len * fr_bytes + RO_TAG_SIZE];
        let mut vals0_offset = 0;
        for kk in 0..input_count {
            let mut localvals0 = vec![];
            let localhashoutput = &hashoutput
                [(2 * vals0_offset * HASH_SIZE)..(2 * (vals0_offset + input_len[kk]) * HASH_SIZE)];
            let localcorrectionvec = &mut correction_vec_raw
                [(vals0_offset * fr_bytes)..((vals0_offset + input_len[kk]) * fr_bytes)];
            for ii in 0..input_len[kk] {
                // primary value; with space at the end for the RO tag (this is more convenient than putting it at the start)
                let v = self.curve.parse_scalar(
                    &localhashoutput[(2 * ii * HASH_SIZE)..((2 * ii + 1) * HASH_SIZE)],
                );
                let val1 = self.curve.parse_scalar(
                    &localhashoutput[((2 * ii + 1) * HASH_SIZE)..((2 * ii + 2) * HASH_SIZE)],
                );

                localcorrectionvec[(ii * fr_bytes)..((ii + 1) * fr_bytes)]
                    .copy_from_slice(&val1.sub(&v).add(input_correlation[kk]).to_bytes());
                localvals0.push(v);
            }
            vals0.push(localvals0);
            vals0_offset = vals0_offset + input_len[kk];
        }
        send.write(&correction_vec_raw[0..total_input_len * fr_bytes])?;

        let mut input_len_offset = 0;
        for kk in 0..input_count {
            let localhasherinput = &mut hasherinput[(input_len_offset * HASH_BLOCK_SIZE)
                ..((input_len_offset + 2 * input_len[kk]) * HASH_BLOCK_SIZE)];
            for ii in 0..input_len[kk] {
                // Map for ii: [ 20B: RO tag | 32B: transposed_seed[ii] ], total: 52B
                // Map for input_len + ii: [ 20B: RO tag | 32B: transposed_seed[ii]^compressed_correlation[jj] ], total: 52B
                let tag = tagrange.next()?;
                localhasherinput
                    [(2 * ii * HASH_BLOCK_SIZE)..(2 * ii * HASH_BLOCK_SIZE + RO_TAG_SIZE)]
                    .copy_from_slice(&tag[..]);
                localhasherinput[((2 * ii + 1) * HASH_BLOCK_SIZE)
                    ..((2 * ii + 1) * HASH_BLOCK_SIZE + RO_TAG_SIZE)]
                    .copy_from_slice(&tag[..]);
            }
            input_len_offset = input_len_offset + 2 * input_len[kk];
        }

        let check_hashoutput = hash_multi(&hasherinput).concat();

        let mut check_correction_vec_raw = vec![0u8; total_input_len * fr_bytes + RO_TAG_SIZE];
        vals0_offset = 0;
        for kk in 0..input_count {
            let mut localcheckvals0 = vec![];
            let localcheckhashoutput = &check_hashoutput
                [(2 * vals0_offset * HASH_SIZE)..(2 * (vals0_offset + input_len[kk]) * HASH_SIZE)];
            let localcheckcorrectionvec = &mut check_correction_vec_raw
                [(vals0_offset * fr_bytes)..((vals0_offset + input_len[kk]) * fr_bytes)];
            for ii in 0..input_len[kk] {
                // check value; with space at the end for the RO tag (this is more convenient than putting it at the start)
                let v = self.curve.parse_scalar(
                    &localcheckhashoutput[(2 * ii * HASH_SIZE)..((2 * ii + 1) * HASH_SIZE)],
                );
                let check_val1 = self.curve.parse_scalar(
                    &localcheckhashoutput[((2 * ii + 1) * HASH_SIZE)..((2 * ii + 2) * HASH_SIZE)],
                );
                localcheckcorrectionvec[(ii * fr_bytes)..((ii + 1) * fr_bytes)]
                    .copy_from_slice(&check_val1.sub(&v).add(&check_alpha[kk]).to_bytes());
                localcheckvals0.push(v);
            }
            check_vals0.push(localcheckvals0);
            vals0_offset = vals0_offset + input_len[kk];
        }
        send.write(&check_correction_vec_raw[0..total_input_len * fr_bytes])?;

        let mut coefs = vec![];
        correction_vec_raw[total_input_len * fr_bytes..].copy_from_slice(&tagrange.next()?[..]);
        let coef_raw = hash(&correction_vec_raw);

        for _ in 0..input_count {
            coefs.push(
                self.curve
                    .parse_scalar(&hash(&[coef_raw.clone(), tagrange.next()?].concat())),
            );
        }

        let mut check_coefs = vec![];
        check_correction_vec_raw[total_input_len * fr_bytes..]
            .copy_from_slice(&tagrange.next()?[..]);
        let check_coef_raw = hash(&check_correction_vec_raw);

        for _ in 0..input_count {
            check_coefs.push(
                self.curve
                    .parse_scalar(&hash(&[check_coef_raw.clone(), tagrange.next()?].concat())),
            );
        }

        let mut check_vec = vec![Scalar::zero(self.curve); *input_len.iter().max().unwrap()];
        for kk in 0..input_count {
            for ii in 0..input_len[kk] {
                check_vec[ii] = check_vec[ii]
                    .add(&vals0[kk][ii].mul(&coefs[kk]))
                    .add(&check_vals0[kk][ii].mul(&check_coefs[kk]));
            }
        }

        let check_vec_raw = check_vec
            .iter()
            .flat_map(|i| i.to_bytes())
            .collect::<Vec<_>>();
        send.write(&check_vec_raw)?;

        let references_raw = (0..input_count)
            .flat_map(|kk| {
                (input_correlation[kk]
                    .mul(&coefs[kk])
                    .add(&check_alpha[kk].mul(&check_coefs[kk])))
                .to_bytes()
            })
            .collect::<Vec<_>>();
        send.write(&references_raw)?;

        Ok(vals0)
    }
}

impl OTERecver {
    pub fn new<T1: Read, T2: Write, R: Rng>(
        curve: &'static Curve,
        ro: &DyadicROTagger,
		rng: &mut R,
        recv: &mut T1,
        send: &mut T2,
    ) -> Result<Self, Box<dyn Error>> {
        let fr_bits = curve.fr_bits;

        let seeds = rot_send_batch(curve, fr_bits, &ro, rng, recv, send)?;
        Ok(OTERecver {
            seeds: seeds,
            curve: curve,
        })
    }

    pub fn apply_refresh(
        &mut self,
        rand: &[u8],
        ro: &DyadicROTagger,
    ) -> Result<(), Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        assert!(rand.len() >= HASH_SIZE);
        let mut expanded_rand = vec![0u8; 2 * HASH_SIZE * fr_bits + fr_bits / 8];
        let mut source_with_tag = vec![0u8; rand.len() + RO_TAG_SIZE];
        source_with_tag[RO_TAG_SIZE..].copy_from_slice(&rand[..]);
        for ii in 0..((expanded_rand.len() + HASH_SIZE - 1) / HASH_SIZE) {
            let offset = ii * HASH_SIZE;
            let remain = min(expanded_rand.len() - offset, HASH_SIZE);
            source_with_tag[0..RO_TAG_SIZE].copy_from_slice(&ro.next_dyadic_tag()[..]);
            expanded_rand[offset..(offset + remain)]
                .copy_from_slice(&hash(&source_with_tag)[0..remain]);
        }

        for ii in 0..fr_bits {
            let correlation_modifier =
                (expanded_rand[2 * HASH_SIZE * fr_bits + ii / 8] >> (ii % 8)) & 1;
            let (seedb, seedinvb) = if correlation_modifier == 1 {
                (&self.seeds[ii].1, &self.seeds[ii].0)
            } else {
                (&self.seeds[ii].0, &self.seeds[ii].1)
            };
            for jj in 0..HASH_SIZE {
                expanded_rand[ii * HASH_SIZE + jj] ^= seedb[jj];
                expanded_rand[HASH_SIZE * fr_bits + ii * HASH_SIZE + jj] ^= seedinvb[jj];
            }
        }

        for ii in 0..fr_bits {
            self.seeds[ii].0[..]
                .copy_from_slice(&expanded_rand[ii * HASH_SIZE..(ii + 1) * HASH_SIZE]);
            self.seeds[ii].1[..].copy_from_slice(
                &expanded_rand[HASH_SIZE * fr_bits + ii * HASH_SIZE
                    ..HASH_SIZE * fr_bits + (ii + 1) * HASH_SIZE],
            );
        }
        return Ok(());
    }

    pub fn extend<T: Write, R: Rng>(
        &self,
        choice_bits_in: &[bool],
        ro: &DyadicROTagger,
        rng: &mut R,
        send: &mut T,
    ) -> Result<Vec<u8>, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        let mut choice_bits = choice_bits_in.to_vec();

        for _ in 0..OT_SEC_PARAM {
            choice_bits.push((rng.next_u32() % 2) > 0);
        }

        let mut compressed_choice_bits: Vec<u8> = Vec::with_capacity(choice_bits.len() / 8);
        for ii in 0..(choice_bits.len() / 8) {
            compressed_choice_bits.push(
                ((choice_bits[ii * 8 + 0] as u8) << 0)
                    | ((choice_bits[ii * 8 + 1] as u8) << 1)
                    | ((choice_bits[ii * 8 + 2] as u8) << 2)
                    | ((choice_bits[ii * 8 + 3] as u8) << 3)
                    | ((choice_bits[ii * 8 + 4] as u8) << 4)
                    | ((choice_bits[ii * 8 + 5] as u8) << 5)
                    | ((choice_bits[ii * 8 + 6] as u8) << 6)
                    | ((choice_bits[ii * 8 + 7] as u8) << 7),
            );
        }

        // Extend phase
        let prgoutputlen = choice_bits.len();
        let mut expanded_seeds0: Vec<u8> = Vec::with_capacity(fr_bytes * prgoutputlen);
        let mut expanded_seeds1: Vec<u8> = Vec::with_capacity(fr_bytes * prgoutputlen);
        let prgiterations = ((prgoutputlen / 8) + HASH_SIZE - 1) / HASH_SIZE;

        let mut tagrange =
            ro.allocate_dyadic_range((fr_bits * prgiterations + prgoutputlen + 1) as u64);

        debug_assert!((fr_bytes * prgoutputlen) % HASH_SIZE == 0);

        let mut hasherinput = vec![0u8; 2 * HASH_BLOCK_SIZE * prgiterations * fr_bits];
        for ii in 0..fr_bits {
            for jj in 0..prgiterations {
                // Map for (ii,jj): [ 20B: RO tag | 32B: seed[ii].0 ], total: 52B
                // Map for (HASH_BLOCK_SIZE*prgiterations*fr_bits+ii,jj): [ 20B RO tag | 32B: seed[ii].1 ], total: 52B
                let tag = tagrange.next()?;
                hasherinput[((ii * prgiterations + jj) * HASH_BLOCK_SIZE)
                    ..((ii * prgiterations + jj) * HASH_BLOCK_SIZE + RO_TAG_SIZE)]
                    .copy_from_slice(&tag[..]);
                hasherinput[((ii * prgiterations + jj) * HASH_BLOCK_SIZE + RO_TAG_SIZE)
                    ..((ii * prgiterations + jj) * HASH_BLOCK_SIZE + RO_TAG_SIZE + HASH_SIZE)]
                    .copy_from_slice(&self.seeds[ii].0);
                hasherinput[(HASH_BLOCK_SIZE * prgiterations * fr_bits
                    + (ii * prgiterations + jj) * HASH_BLOCK_SIZE)
                    ..(HASH_BLOCK_SIZE * prgiterations * fr_bits
                        + (ii * prgiterations + jj) * HASH_BLOCK_SIZE
                        + RO_TAG_SIZE)]
                    .copy_from_slice(&tag[..]);
                hasherinput[(HASH_BLOCK_SIZE * prgiterations * fr_bits
                    + (ii * prgiterations + jj) * HASH_BLOCK_SIZE
                    + RO_TAG_SIZE)
                    ..(HASH_BLOCK_SIZE * prgiterations * fr_bits
                        + (ii * prgiterations + jj) * HASH_BLOCK_SIZE
                        + RO_TAG_SIZE
                        + HASH_SIZE)]
                    .copy_from_slice(&self.seeds[ii].1);
            }
        }

        let prgoutput = hash_multi(&hasherinput).concat();

        for ii in 0..fr_bits {
            expanded_seeds0.extend_from_slice(
                &prgoutput[(ii * prgiterations * HASH_SIZE)
                    ..(ii * prgiterations * HASH_SIZE + prgoutputlen / 8)],
            );
            expanded_seeds1.extend_from_slice(
                &prgoutput[(HASH_SIZE * prgiterations * fr_bits + ii * prgiterations * HASH_SIZE)
                    ..(HASH_SIZE * prgiterations * fr_bits
                        + ii * prgiterations * HASH_SIZE
                        + prgoutputlen / 8)],
            );
        }

        let transposed_seed0 = transpose(&expanded_seeds0, prgoutputlen / 8);

        debug_assert!(expanded_seeds0.len() / compressed_choice_bits.len() == fr_bits);

        let mut seeds_combined = vec![0u8; fr_bytes * prgoutputlen + RO_TAG_SIZE];
        for ii in 0..expanded_seeds0.len() {
            seeds_combined[ii] = expanded_seeds0[ii]
                ^ expanded_seeds1[ii]
                ^ compressed_choice_bits[ii % compressed_choice_bits.len()];
        }

        let mut hash_input = vec![];
        seeds_combined[(fr_bytes * prgoutputlen)..].copy_from_slice(&tagrange.next()?[..]);
        let mut seeds_shortened = hash(&seeds_combined);

        for _ in 0..prgoutputlen {
            // Map for ii: [ 20B RO tag | 32B: seeds_shortened ], total: 52B
            hash_input.extend_from_slice(&tagrange.next()?);
            hash_input.extend_from_slice(&seeds_shortened);
            hash_input.extend_from_slice(&[0; HASH_BLOCK_SIZE - HASH_SIZE - RO_TAG_SIZE]);
        }
        let random_samples = hash_multi(&hash_input).concat();

        debug_assert!(expanded_seeds0.len() == transposed_seed0.len());
        debug_assert!(transposed_seed0.len() == random_samples.len());

        let mut sampled_bits = vec![0u8; fr_bytes];
        let mut sampled_seeds = vec![0u8; fr_bytes];
        for ii in 0..prgoutputlen {
            if choice_bits[ii] {
                for jj in 0..fr_bytes {
                    sampled_bits[jj] ^= random_samples[ii * fr_bytes + jj];
                }
            }
            for jj in 0..fr_bytes {
                sampled_seeds[jj] ^=
                    transposed_seed0[ii * fr_bytes + jj] & random_samples[ii * fr_bytes + jj];
            }
        }

        let mut bufsend = BufWriter::new(send);
        bufsend.write(&seeds_combined[0..fr_bytes * prgoutputlen])?;
        bufsend.write(&sampled_bits)?;
        bufsend.write(&sampled_seeds)?;

        Ok(transposed_seed0)
    }

    pub fn transfer<T: Read>(
        &self,
        choice_bits: &[Vec<bool>],
        transposed_seed: &[Vec<u8>],
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> Result<Vec<Vec<Scalar>>, Box<dyn Error>> {
        let fr_bytes = self.curve.fr_bytes;
        let input_count = choice_bits.len();
        let total_input_len = choice_bits.iter().map(|x| x.len()).sum();
        let mut tagrange =
            ro.allocate_dyadic_range((2 * total_input_len + 2 * input_count + 2) as u64);

        let mut hasherinput = transposed_seed
            .iter()
            .flat_map(|seed| seed.chunks(HASH_SIZE))
            .flat_map(|seed| {
                let tag = tagrange.next().unwrap();
                [
                    tag.clone(),
                    seed.to_vec(),
                    vec![0; HASH_BLOCK_SIZE - HASH_SIZE - RO_TAG_SIZE],
                ]
                .concat()
            })
            .collect::<Vec<_>>();

        let hashoutput = hash_multi(&hasherinput).concat();

        for ii in 0..total_input_len {
            // Map for ii: [ 20B RO tag | 32B: transposed_seed[ii] ], total: 52B
            hasherinput[(ii * HASH_BLOCK_SIZE)..(ii * HASH_BLOCK_SIZE + RO_TAG_SIZE)]
                .copy_from_slice(&tagrange.next()?);
        }

        let check_hashoutput = hash_multi(&hasherinput);

        let mut correction_vec_raw = vec![0u8; total_input_len * fr_bytes + RO_TAG_SIZE];
        recv.read_exact(&mut correction_vec_raw[0..total_input_len * fr_bytes])?;
        correction_vec_raw[total_input_len * fr_bytes..].copy_from_slice(&tagrange.next()?[..]);

        let mut coef_seed = [0u8; HASH_SIZE + RO_TAG_SIZE];
        let mut coef_raw = hash(&correction_vec_raw);
        let mut coefs = vec![];

        coef_seed[0..HASH_SIZE].copy_from_slice(&coef_raw);
        for _ in 0..input_count {
            coef_seed[HASH_SIZE..].copy_from_slice(&tagrange.next()?[..]);
            coef_raw = hash(&coef_seed);
            coefs.push(self.curve.parse_scalar(&coef_raw));
        }

        let mut vals = Vec::with_capacity(input_count);
        let mut vals_offset = 0;
        for kk in 0..input_count {
            let mut localvals = vec![];
            let localhashoutput = &hashoutput
                [(vals_offset * HASH_SIZE)..((vals_offset + choice_bits[kk].len()) * HASH_SIZE)];
            let localcorrectionvec = &mut correction_vec_raw
                [(vals_offset * fr_bytes)..((vals_offset + choice_bits[kk].len()) * fr_bytes)];

            for ii in 0..choice_bits[kk].len() {
                let cv = self
                    .curve
                    .parse_scalar(&localcorrectionvec[(ii * fr_bytes)..((ii + 1) * fr_bytes)]);
                let val = self
                    .curve
                    .parse_scalar(&localhashoutput[(ii * HASH_SIZE)..((ii + 1) * HASH_SIZE)])
                    .neg();
                let val_aug = val.add(&cv);
                localvals.push(if choice_bits[kk][ii] { val_aug } else { val });
            }
            vals.push(localvals);
            vals_offset = vals_offset + choice_bits[kk].len();
        }

        let mut check_correction_vec_raw = vec![0u8; total_input_len * fr_bytes + RO_TAG_SIZE];
        check_correction_vec_raw[total_input_len * fr_bytes..]
            .copy_from_slice(&tagrange.next()?[..]);
        recv.read_exact(&mut check_correction_vec_raw[0..total_input_len * fr_bytes])?;

        let mut check_coef_seed = [0u8; HASH_SIZE + RO_TAG_SIZE];
        let mut check_coef_raw = hash(&check_correction_vec_raw);
        let mut check_coefs = vec![];

        check_coef_seed[0..HASH_SIZE].copy_from_slice(&check_coef_raw);

        for kk in 0..input_count {
            check_coef_seed[HASH_SIZE..].copy_from_slice(&tagrange.next()?[..]);
            check_coef_raw = hash(&check_coef_seed);
            check_coefs.push(self.curve.parse_scalar(&check_coef_raw));
        }

        let mut check_vals = Vec::with_capacity(input_count);
        vals_offset = 0;
        for kk in 0..input_count {
            let mut localcheckvals = vec![];
            let localcheckhashoutput = &check_hashoutput
                [(vals_offset)..((vals_offset + choice_bits[kk].len()))];
            let localcheckcorrectionvec = &mut check_correction_vec_raw
                [(vals_offset * fr_bytes)..((vals_offset + choice_bits[kk].len()) * fr_bytes)];

            for ii in 0..choice_bits[kk].len() {
                let ccv = self
                    .curve
                    .parse_scalar(&localcheckcorrectionvec[(ii * fr_bytes)..((ii + 1) * fr_bytes)]);
                let check_val = self
                    .curve
                    .parse_scalar(&localcheckhashoutput[ii])
                    .neg();
                let check_val_aug = check_val.add(&ccv);
                localcheckvals.push(if choice_bits[kk][ii] {
                    check_val_aug
                } else {
                    check_val
                });
            }
            check_vals.push(localcheckvals);
            vals_offset = vals_offset + choice_bits[kk].len();
        }

        let mut check_vec_raw =
            vec![0u8; choice_bits.iter().map(|x| x.len()).max().unwrap() * fr_bytes];
        recv.read_exact(&mut check_vec_raw)?;
        let mut references = Vec::with_capacity(input_count);
        for _ in 0..input_count {
            let mut reference_raw = vec![0u8; fr_bytes];
            recv.read_exact(&mut reference_raw)?;
            references.push(self.curve.parse_scalar(&reference_raw));
        }

        for ii in 0..choice_bits.iter().map(|x| x.len()).max().unwrap() {
            let mut rhs = self
                .curve
                .parse_scalar(&check_vec_raw[(ii * fr_bytes)..((ii + 1) * fr_bytes)])
                .neg();
            let mut lhs = Scalar::zero(self.curve);
            for kk in 0..input_count {
                if (ii < choice_bits[kk].len()) && (choice_bits[kk][ii]) {
                    rhs = rhs.add(&references[kk]);
                }
                if ii < choice_bits[kk].len() {
                    lhs = (lhs
                        .add(&vals[kk][ii].mul(&coefs[kk]))
                        .add(&check_vals[kk][ii].mul(&check_coefs[kk])));
                }
            }

            assert_eq!(lhs, rhs);
        }
        Ok(vals)
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::P521;

    use super::channelstream::*;
    use super::*;
    use byteorder::{ByteOrder, LittleEndian};
    use rand::RngCore;
    use std::thread;

    #[test]
    fn test_transpose8x8() {
        let a = 0b0111101000011101000100010111010000001010000000010010111111111111;
        let at = 0b0000000110010001100100111111000111001011010100111000101101100111;
        let b = transpose8x8(a);
        assert!(b == at);

        let a = 0b1111001111001000110101111000000100111110000101011001110000011100;
        let at = 0b1111001011100000100010001010111101001011001011111010100010110100;
        let b = transpose8x8(a);
        assert!(b == at);
    }

    #[test]
    fn test_transpose() {
        let mut a: Vec<u8> = vec![0u8; 16];
        let mut at: Vec<u8> = vec![0u8; 16];
        LittleEndian::write_u64(
            &mut a[0..8],
            0b0111101001111010000111010001110100010001000100010111010001110100,
        );
        LittleEndian::write_u64(
            &mut a[8..16],
            0b0000101000001010000000010000000100101111001011111111111111111111,
        );

        LittleEndian::write_u64(
            &mut at[0..8],
            0b0000100010011000100111001111100000111101101011000001110101101110u64
                .swap_bits()
                .swap_bytes(),
        );
        LittleEndian::write_u64(
            &mut at[8..16],
            0b0000100010011000100111001111100000111101101011000001110101101110u64
                .swap_bits()
                .swap_bytes(),
        );

        let b = transpose(&a, 2);
        assert!(b == at);
    }

    #[test]
    fn test_ote_setup() {
        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(2);

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let child = thread::spawn(move || {
            let mut rng = rand::thread_rng();

            let ro = {
                let mut r1ref = r1
                    .iter_mut()
                    .map(|x| if x.is_some() { x.as_mut() } else { None })
                    .collect::<Vec<Option<&mut _>>>();
                let mut s1ref = s1
                    .iter_mut()
                    .map(|x| if x.is_some() { x.as_mut() } else { None })
                    .collect::<Vec<Option<&mut _>>>();
                GroupROTagger::from_network_unverified(0, &mut rng, &mut r1ref[..], &mut s1ref[..])
            };
            let sender = OTESender::new(
                &P521,
                &ro.get_dyadic_tagger(1),
				&mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            )
            .unwrap();
            sender
        });

        let mut rng = rand::thread_rng();

        let ro = {
            let mut r2ref = r2
                .iter_mut()
                .map(|x| if x.is_some() { x.as_mut() } else { None })
                .collect::<Vec<Option<&mut _>>>();
            let mut s2ref = s2
                .iter_mut()
                .map(|x| if x.is_some() { x.as_mut() } else { None })
                .collect::<Vec<Option<&mut _>>>();
            GroupROTagger::from_network_unverified(1, &mut rng, &mut r2ref[..], &mut s2ref[..])
        };
        let recver = OTERecver::new(
            &P521,
            &ro.get_dyadic_tagger(0),
			&mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();

        let sender = child.join().unwrap();
        assert!(sender.correlation.len() > 0);
        sender
            .seeds
            .into_iter()
            .zip(recver.seeds)
            .zip(sender.correlation)
            .for_each(|((s1, s2), c)| {
                assert_eq!(s1, if c { s2.1 } else { s2.0 });
            });
    }

    #[test]
    fn test_ote_refresh() {
        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(2);

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let child = thread::spawn(move || {
            let mut rng = rand::thread_rng();

            let ro = {
                let mut r1ref = r1
                    .iter_mut()
                    .map(|x| if x.is_some() { x.as_mut() } else { None })
                    .collect::<Vec<Option<&mut _>>>();
                let mut s1ref = s1
                    .iter_mut()
                    .map(|x| if x.is_some() { x.as_mut() } else { None })
                    .collect::<Vec<Option<&mut _>>>();
                GroupROTagger::from_network_unverified(0, &mut rng, &mut r1ref[..], &mut s1ref[..])
            };
            let sender = OTESender::new(
                &P521,
                &ro.get_dyadic_tagger(1),
				&mut rng,
				r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            )
            .unwrap();
            (ro, sender)
        });

        let mut rng = rand::thread_rng();

        let ror = {
            let mut r2ref = r2
                .iter_mut()
                .map(|x| if x.is_some() { x.as_mut() } else { None })
                .collect::<Vec<Option<&mut _>>>();
            let mut s2ref = s2
                .iter_mut()
                .map(|x| if x.is_some() { x.as_mut() } else { None })
                .collect::<Vec<Option<&mut _>>>();
            GroupROTagger::from_network_unverified(1, &mut rng, &mut r2ref[..], &mut s2ref[..])
        };
        let mut recver = OTERecver::new(
            &P521,
            &ror.get_dyadic_tagger(0),
			&mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();

        let (ros, mut sender) = child.join().unwrap();

        let mut refreshval = [0u8; HASH_SIZE];
        rng.fill_bytes(&mut refreshval);

        sender
            .apply_refresh(&refreshval, &ros.get_dyadic_tagger(1))
            .unwrap();
        recver
            .apply_refresh(&refreshval, &ror.get_dyadic_tagger(0))
            .unwrap();

        rng.fill_bytes(&mut refreshval);

        sender
            .apply_refresh(&refreshval, &ros.get_dyadic_tagger(1))
            .unwrap();
        recver
            .apply_refresh(&refreshval, &ror.get_dyadic_tagger(0))
            .unwrap();

        rng.fill_bytes(&mut refreshval);

        sender
            .apply_refresh(&refreshval, &ros.get_dyadic_tagger(1))
            .unwrap();
        recver
            .apply_refresh(&refreshval, &ror.get_dyadic_tagger(0))
            .unwrap();

        assert!(sender.correlation.len() > 0);
        for ii in 0..sender.correlation.len() {
            assert_eq!(
                sender.seeds[ii],
                if sender.correlation[ii] {
                    recver.seeds[ii].1.clone()
                } else {
                    recver.seeds[ii].0.clone()
                }
            );
        }

        rng.fill_bytes(&mut refreshval);
        sender
            .apply_refresh(&refreshval, &ros.get_dyadic_tagger(1))
            .unwrap();

        rng.fill_bytes(&mut refreshval);
        recver
            .apply_refresh(&refreshval, &ror.get_dyadic_tagger(0))
            .unwrap();

        for ii in 0..sender.correlation.len() {
            assert_ne!(
                sender.seeds[ii],
                if sender.correlation[ii] {
                    recver.seeds[ii].1.clone()
                } else {
                    recver.seeds[ii].0.clone()
                }
            );
        }
    }
}
