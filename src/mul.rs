/***********
 * This module implements the two-party multiplication protocol
 * described in the paper "Secure Two-party Threshold ECDSA from ECDSA Assumptions"
 * by Doerner, Kondi, Lee, and shelat (https://eprint.iacr.org/2018/499)
 *
 * It also implements the two-party random multiplication protocol
 * described in the paper "Threshold ECDSA from ECDSA Assumptions"
 * by Doerner, Kondi, Lee, and shelat
 *
 * Both multipliers rely upon the KOS OT-extension protocol in ote.rs
 ***********/

use rand::Rng;
use std::cmp;
use std::result::Result;
use std::thread;
use std::time::Instant;

use crate::channelstream::spawn_n2_channelstreams;
use crate::utils::Curve;
use crate::utils::P521;
use crate::utils::Scalar;

use super::ote::*;
use super::ro::*;
use super::*;
use std::error::Error;

//#[derive(Clone)]
pub struct MulSender {
    publicrandomvec: Vec<Scalar>,
    ote: OTESender,
    curve: &'static Curve,
}

//#[derive(Clone)]
pub struct MulRecver {
    publicrandomvec: Vec<Scalar>,
    ote: OTERecver,
    curve: &'static Curve,
}

//#[derive(Clone)]
pub enum MulPlayer {
    Sender(MulSender),
    Recver(MulRecver),
    Null,
}

pub type RmulSenderData = (Vec<Vec<u8>>, Vec<u8>, Vec<Scalar>);
pub type MulRecverData = (Vec<Vec<bool>>, Vec<bool>, Vec<Vec<u8>>, Vec<u8>);
pub type RmulRecverData = (
    Vec<Vec<bool>>,
    Vec<bool>,
    Vec<Vec<u8>>,
    Vec<u8>,
    Vec<Scalar>,
);

impl MulSender {
    pub fn new<T1: Read, T2: Write, R: Rng>(
        curve: &'static Curve,
        ro: &DyadicROTagger,
        rng: &mut R,
        recv: &mut T1,
        send: &mut T2,
    ) -> Self {
        let fr_bits = curve.fr_bits;
        let fr_bytes = curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;
        let RAND_ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        let total_bits = cmp::max(
            fr_bits + ENCODING_PER_ELEMENT_BITS + ENCODING_EXTRA_BITS,
            RAND_ENCODING_PER_ELEMENT_BITS + RAND_ENCODING_EXTRA_BITS,
        );

        let mut raw_nonce = vec![0u8; fr_bytes];
        recv.read_exact(&mut raw_nonce).unwrap();
        let mut nonce = curve.parse_scalar(&raw_nonce);
        let publicrandomvec = (0..total_bits)
            .map(|_| {
                nonce = Scalar::one(curve).add(&nonce);
                curve.parse_scalar(&hash(&nonce.to_bytes()))
            })
            .collect();

        let ote = OTESender::new(curve, ro, rng, recv, send).unwrap();

        MulSender {
            publicrandomvec: publicrandomvec,
            ote: ote,
            curve,
        }
    }

    pub fn apply_refresh(
        &mut self,
        rand: &[u8],
        ro: &DyadicROTagger,
    ) -> Result<(), Box<dyn Error>> {
        return self.ote.apply_refresh(rand, ro);
    }

    pub fn mul_extend<T: Read>(
        &self,
        input_count: usize,
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> (Vec<Vec<u8>>, Vec<u8>) {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        let transposed_seed = self
            .ote
            .extend(
                input_count * (fr_bits + ENCODING_PER_ELEMENT_BITS) + ENCODING_EXTRA_BITS,
                ro,
                recv,
            )
            .unwrap();

        (
            transposed_seed
                .chunks_exact((fr_bits + ENCODING_PER_ELEMENT_BITS) * HASH_SIZE)
                .map(|i| i.to_vec())
                .collect(),
            transposed_seed[(input_count * (fr_bits + ENCODING_PER_ELEMENT_BITS) * HASH_SIZE)
                ..(input_count * (fr_bits + ENCODING_PER_ELEMENT_BITS) * HASH_SIZE
                    + ENCODING_EXTRA_BITS * HASH_SIZE)]
                .try_into()
                .unwrap(),
        )
    }

    pub fn mul_transfer<T: Write, R: Rng>(
        &self,
        inputs_alpha: &[&Scalar],
        transposed_seed_fragment: &[Vec<u8>],
        transposed_seed_encoding_fragment: &[u8],
        ro: &DyadicROTagger,
        rng: &mut R,
        send: &mut T,
    ) -> Result<Vec<Scalar>, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        let transposed_seeds = transposed_seed_fragment
            .iter()
            .map(|fragment| {
                [
                    fragment.to_vec(),
                    transposed_seed_encoding_fragment.to_vec(),
                ]
                .concat()
            })
            .collect::<Vec<_>>();

        let vals0 = self.ote.transfer(
            &vec![
                fr_bits + ENCODING_PER_ELEMENT_BITS + ENCODING_EXTRA_BITS;
                transposed_seed_fragment.len()
            ],
            inputs_alpha,
            &transposed_seeds,
            ro,
            rng,
            send,
        )?;

        Ok(vals0
            .iter()
            .map(|val| {
                let mut result = Scalar::zero(self.curve);

                for ii in 0..((fr_bits + ENCODING_PER_ELEMENT_BITS) + ENCODING_EXTRA_BITS) {
                    // primary value
                    let offset = if ii < fr_bits {
                        (Scalar::two_to_n(self.curve, fr_bits - (ii / 8) * 8 - 8 + (ii % 8)))
                    } else {
                        self.publicrandomvec[(ii / 8) * 8 - fr_bits + ii % 8].clone()
                    };
                    result = result.add(&val[ii].mul(&offset));
                }
                result
            })
            .collect())
    }

    pub fn rmul_extend<T: Read, R: Rng>(
        &self,
        input_count: usize,
        ro: &DyadicROTagger,
        rng: &mut R,
        recv: &mut T,
    ) -> Result<RmulSenderData, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let RAND_ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        let transposed_seed = self.ote.extend(
            input_count * RAND_ENCODING_PER_ELEMENT_BITS + RAND_ENCODING_EXTRA_BITS,
            ro,
            recv,
        )?;

        Ok((
            transposed_seed
                .chunks_exact(HASH_SIZE * RAND_ENCODING_PER_ELEMENT_BITS)
                .map(|i| i.to_vec())
                .collect(),
            transposed_seed[(input_count * RAND_ENCODING_PER_ELEMENT_BITS * HASH_SIZE)
                ..(input_count * RAND_ENCODING_PER_ELEMENT_BITS * HASH_SIZE
                    + RAND_ENCODING_EXTRA_BITS * HASH_SIZE)]
                .try_into()
                .unwrap(),
            (0..input_count).map(|_| self.curve.rand_scalar(rng)).collect(),
        ))
    }

    pub fn rmul_transfer<T: Write, R: Rng>(
        &self,
        inputs_alpha: &[&Scalar],
        transposed_seed_fragment: &[Vec<u8>],
        transposed_seed_encoding_fragment: &[u8],
        ro: &DyadicROTagger,
        rng: &mut R,
        send: &mut T,
    ) -> Result<Vec<Scalar>, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let RAND_ENCODING_PER_ELEMENT_BITS = fr_bits + 160;
        let vals0 = &self.ote.transfer(
            &vec![
                RAND_ENCODING_PER_ELEMENT_BITS + RAND_ENCODING_EXTRA_BITS;
                transposed_seed_fragment.len()
            ],
            inputs_alpha,
            &transposed_seed_fragment
                .iter()
                .map(|fragment| {
                    [
                        fragment.to_vec(),
                        transposed_seed_encoding_fragment.to_vec(),
                    ]
                    .concat()
                })
                .collect::<Vec<_>>(),
            ro,
            rng,
            send,
        )?;

        Ok(vals0
            .iter()
            .map(|val| {
                let mut result = Scalar::zero(self.curve);

                for ii in 0..(RAND_ENCODING_PER_ELEMENT_BITS + RAND_ENCODING_EXTRA_BITS) {
                    // primary value
                    let offset = &self.publicrandomvec[(ii / 8) * 8 + ii % 8];
                    result = result.add(&val[ii].mul(offset));
                }
                result
            })
            .collect())
    }
}

impl MulRecver {
    pub fn new<T1: Read, T2: Write, R: Rng>(
        curve: &'static Curve,
        ro: &DyadicROTagger,
        rng: &mut R,
        recv: &mut T1,
        send: &mut T2,
    ) -> Result<Self, Box<dyn Error>> {
        let fr_bits = curve.fr_bits;
        let fr_bytes = curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;
        let RAND_ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        //ROT sender goes first, so we let the OTExt recver choose the public random vector to reduce rounds.
        let total_bits = cmp::max(
            fr_bits + ENCODING_PER_ELEMENT_BITS + ENCODING_EXTRA_BITS,
            RAND_ENCODING_PER_ELEMENT_BITS + RAND_ENCODING_EXTRA_BITS,
        );

        let mut nonce = curve.rand_scalar(rng);
        send.write(&nonce.to_bytes())?;
        send.flush()?;

        Ok(MulRecver {
            publicrandomvec: (0..total_bits)
                .map(|_| {
                    nonce = Scalar::one(curve).add(&nonce);
                    curve.parse_scalar(&hash(&nonce.to_bytes()))
                })
                .collect(),
            ote: OTERecver::new(curve, ro, rng, recv, send)?,
            curve,
        })
    }

    pub fn apply_refresh(
        &mut self,
        rand: &[u8],
        ro: &DyadicROTagger,
    ) -> Result<(), Box<dyn Error>> {
        return self.ote.apply_refresh(rand, ro);
    }

    pub fn mul_encode_and_extend<T: Write, R: Rng>(
        &self,
        inputs_beta: &[Scalar],
        ro: &DyadicROTagger,
        rng: &mut R,
        send: &mut T,
    ) -> Result<MulRecverData, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;
        // Encode phase
        let mut encoding_private_bits = vec![false; ENCODING_EXTRA_BITS];
        let mut encoding_private_offset = Scalar::zero(self.curve);
        for ii in 0..ENCODING_EXTRA_BITS {
            encoding_private_bits[ii] = rng.gen_bool(0.5);
            let potential_offset =
                encoding_private_offset.add(&self.publicrandomvec[ENCODING_PER_ELEMENT_BITS + ii]);
            if encoding_private_bits[ii] {
                encoding_private_offset = potential_offset;
            }
        }

        let mut encoding_private_element_bits =
            vec![vec![false; ENCODING_PER_ELEMENT_BITS]; inputs_beta.len()];
        let mut encoding_private_element_offsets =
            vec![Scalar::zero(self.curve); inputs_beta.len()];
        for jj in 0..inputs_beta.len() {
            for ii in 0..ENCODING_PER_ELEMENT_BITS {
                encoding_private_element_bits[jj][ii] = (rng.next_u32() % 2) > 0;
                let potential_offset =
                    encoding_private_element_offsets[jj].add(&self.publicrandomvec[ii]);
                if encoding_private_element_bits[jj][ii] {
                    encoding_private_element_offsets[jj] = potential_offset;
                }
            }
        }

        let mut inputs_encoded = vec![];
        for ii in 0..inputs_beta.len() {
            let beta_aug = inputs_beta[ii]
                .sub(&encoding_private_offset)
                .sub(&encoding_private_element_offsets[ii]);
                let beta_aug_bytes = beta_aug.to_bytes();
            let mut v = (0..fr_bits)
                .map(|jj| (beta_aug_bytes[(jj >> 3)] >> (jj % 8)) & 1 == 1)
                .collect::<Vec<_>>();
            v.extend_from_slice(&encoding_private_element_bits[ii]);
            inputs_encoded.push(v);
        }
        let mut choice_bits = inputs_encoded.concat();
        choice_bits.extend_from_slice(&encoding_private_bits);

        let transposed_seed0 = self.ote.extend(&choice_bits, ro, rng, send)?;

        Ok(
            (
                inputs_encoded,
                encoding_private_bits,
                transposed_seed0
                    .chunks_exact((fr_bits + ENCODING_PER_ELEMENT_BITS) * HASH_SIZE)
                    .map(|i| i.to_vec())
                    .collect(),
                transposed_seed0[(inputs_beta.len()
                    * (fr_bits + ENCODING_PER_ELEMENT_BITS)
                    * HASH_SIZE)
                    ..(inputs_beta.len() * (fr_bits + ENCODING_PER_ELEMENT_BITS) * HASH_SIZE
                        + ENCODING_EXTRA_BITS * HASH_SIZE)]
                    .try_into()
                    .unwrap(),
            ),
        )
    }

    pub fn mul_transfer<T: Read>(
        &self,
        inputs_beta_encoded: &[Vec<bool>],
        encoding_private_bits: &[bool],
        transposed_seed_fragment: &[Vec<u8>],
        transposed_seed_encoding_fragment: &[u8],
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> Result<Vec<Scalar>, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let fr_bytes = self.curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        let transposed_seeds = transposed_seed_fragment
            .into_iter()
            .map(|i| [i, transposed_seed_encoding_fragment].concat())
            .collect::<Vec<_>>();
        let choice_bitss = inputs_beta_encoded
            .into_iter()
            .map(|i| [i, encoding_private_bits].concat())
            .collect::<Vec<_>>();

        Ok(self
            .ote
            .transfer(&choice_bitss, &transposed_seeds, ro, recv)?
            .iter()
            .map(|vals| {
                let mut result = Scalar::zero(self.curve);
                for ii in 0..(fr_bits + ENCODING_PER_ELEMENT_BITS + ENCODING_EXTRA_BITS) {
                    let offset = if ii < fr_bits {
                        (Scalar::two_to_n(self.curve, fr_bits - (ii / 8) * 8 - 8 + (ii % 8)))
                    } else {
                        self.publicrandomvec[(ii / 8) * 8 - fr_bits + ii % 8].clone()
                    };
                    result = result.add(&offset.mul(&vals[ii]));
                }
                result
            })
            .collect())
    }

    pub fn rmul_encode_and_extend<T: Write, R: Rng>(
        &self,
        input_count: usize,
        ro: &DyadicROTagger,
        rng: &mut R,
        send: &mut T,
    ) -> Result<RmulRecverData, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let RAND_ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        // Encode phase
        let mut encoding_private_bits = vec![false; RAND_ENCODING_EXTRA_BITS];
        let mut encoding_private_joint = Scalar::zero(self.curve);
        for ii in 0..RAND_ENCODING_EXTRA_BITS {
            encoding_private_bits[ii] = rng.gen_bool(0.5);
            let potential_offset = encoding_private_joint
                .add(&self.publicrandomvec[RAND_ENCODING_PER_ELEMENT_BITS + ii]);
            if encoding_private_bits[ii] {
                encoding_private_joint = potential_offset;
            }
        }

        let mut encoding_private_random_bits =
            vec![vec![false; RAND_ENCODING_PER_ELEMENT_BITS]; input_count];
        let mut encoding_private_random = vec![Scalar::zero(self.curve); input_count];
        for jj in 0..input_count {
            for ii in 0..RAND_ENCODING_PER_ELEMENT_BITS {
                encoding_private_random_bits[jj][ii] = rng.gen_bool(0.5);
                let potential_offset = encoding_private_random[jj].add(&self.publicrandomvec[ii]);
                if encoding_private_random_bits[jj][ii] {
                    encoding_private_random[jj] = potential_offset;
                }
            }
        }

        let offsets = encoding_private_random
            .iter()
            .map(|i| encoding_private_joint.add(i))
            .collect();
        let mut choice_bits = encoding_private_random_bits.concat();
        choice_bits.extend_from_slice(&encoding_private_bits);

        let transposed_seed0 = self.ote.extend(&choice_bits, ro, rng, send)?;

        Ok((
            encoding_private_random_bits,
            encoding_private_bits,
            transposed_seed0
                .chunks_exact(RAND_ENCODING_PER_ELEMENT_BITS * HASH_SIZE)
                .map(|i| i.to_vec())
                .collect(),
            transposed_seed0[(input_count * RAND_ENCODING_PER_ELEMENT_BITS * HASH_SIZE)
                ..(input_count * RAND_ENCODING_PER_ELEMENT_BITS * HASH_SIZE
                    + ENCODING_EXTRA_BITS * HASH_SIZE)]
                .try_into()
                .unwrap(),
            offsets,
        ))
    }

    pub fn rmul_transfer<T: Read>(
        &self,
        inputs_beta_encoded: &[Vec<bool>],
        encoding_private_bits: &[bool],
        transposed_seed_fragment: &[Vec<u8>],
        transposed_seed_encoding_fragment: &[u8],
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> Result<Vec<Scalar>, Box<dyn Error>> {
        let fr_bits = self.curve.fr_bits;
        let RAND_ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

        let transposed_seeds = transposed_seed_fragment
            .into_iter()
            .map(|i| [i, transposed_seed_encoding_fragment].concat())
            .collect::<Vec<_>>();
        let choice_bitss = inputs_beta_encoded
            .into_iter()
            .map(|i| [i, encoding_private_bits].concat())
            .collect::<Vec<_>>();

        Ok(self
            .ote
            .transfer(&choice_bitss, &transposed_seeds, ro, recv)?
            .iter()
            .map(|vals| {
                let mut result = Scalar::zero(self.curve);
                for ii in 0..(RAND_ENCODING_PER_ELEMENT_BITS + RAND_ENCODING_EXTRA_BITS) {
                    let offset = &self.publicrandomvec[(ii / 8) * 8 + ii % 8];
                    result = result.add(&offset.mul(&vals[ii]));
                }
                result
            })
            .collect())
    }
}

pub fn mul_transfer_fully(
    curve: &'static Curve,
    alpha: Scalar,
    beta: Vec<Scalar>,
) -> (Scalar, Scalar, u128) {
    let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(2);
    let mut s1 = sendvec.remove(0);
    let mut r1 = recvvec.remove(0);
    let mut s2 = sendvec.remove(0);
    let mut r2 = recvvec.remove(0);
    let mut rng = rand::thread_rng();

    let send_thread = thread::spawn(move || {
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
        let dro = ro.get_dyadic_tagger(1);
        let start = Instant::now();
        let sender = MulSender::new(
            curve,
            &ro.get_dyadic_tagger(1),
            &mut rng,
            r1[1].as_mut().unwrap(),
            s1[1].as_mut().unwrap(),
        );
        let time = start.elapsed().as_nanos();
        let extensions = sender.mul_extend(1, &dro, r1[1].as_mut().unwrap());

        let ta1 = sender
            .mul_transfer(
                &[&alpha],
                &extensions.0,
                &extensions.1,
                &dro,
                &mut rng,
                s1[1].as_mut().unwrap(),
            )
            .unwrap()[0]
            .clone();

        (ta1, time)
    });

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

    let dro = ro.get_dyadic_tagger(0);

    let recver = MulRecver::new(
        curve,
        &ro.get_dyadic_tagger(0),
        &mut rng,
        r2[0].as_mut().unwrap(),
        s2[0].as_mut().unwrap(),
    )
    .unwrap();

    let extensions = recver
        .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
        .unwrap();
    let tb1 = recver
        .mul_transfer(
            &[extensions.0[0].clone()],
            &extensions.1,
            &[extensions.2[0].clone()],
            &extensions.3,
            &dro,
            r2[0].as_mut().unwrap(),
        )
        .unwrap()[0]
        .clone();
    let (ta1, time) = send_thread.join().unwrap();
    //time is the time of new()
    return (ta1, tb1, time);
}

#[test]
fn test_mul_trans1(){
    let curve = &P521;
 let mut rng = rand::thread_rng();
 let alpha = curve.rand_scalar(&mut rng);
 let mut beta:Vec<Scalar> = Vec::with_capacity(10);
    beta.push(curve.rand_scalar(&mut rng));
    let timer1 = Instant::now();
    //for i in 0.. 100{
  //beta.push(SecpOrd::rand(&mut rng));
  let (ta, tb, time) = mul_transfer_fully(curve, alpha.clone(), beta.clone());
    //}
 println!("total time: {:?}ns", timer1.elapsed().as_nanos()-time.clone());
}

#[cfg(test)]
mod tests {
    use crate::utils::{P521, K256, P384};

    use super::channelstream::*;
    use super::*;
    use std::thread;
    use std::time::Instant;
    use rand::RngCore;
    use test::Bencher;


    #[test]
    fn test_mul_mul_extend() {
        let curve = &P521;
        let fr_bits = curve.fr_bits;
        let fr_bytes = curve.fr_bytes;
        let ENCODING_PER_ELEMENT_BITS = fr_bits + 160;

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
            let sender = MulSender::new(
                curve,
                &ro.get_dyadic_tagger(1),
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            sender.mul_extend(2, &ro.get_dyadic_tagger(1), r1[1].as_mut().unwrap())
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

        let recver = MulRecver::new(
            curve,
            &ro.get_dyadic_tagger(0),
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();

        let mut beta = Vec::with_capacity(2);
        for _ in 0..2 {
            beta.push(curve.rand_scalar(&mut rng));
        }
        let recver_result = recver.mul_encode_and_extend(
            &beta,
            &ro.get_dyadic_tagger(0),
            &mut rng,
            s2[0].as_mut().unwrap(),
        );
        assert!(recver_result.is_ok());
        let recver_result = recver_result.unwrap();

        let mut encoding_offset = Scalar::zero(curve);
        for ii in 0..ENCODING_EXTRA_BITS {
            if recver_result.1[ii] {
                encoding_offset =
                    encoding_offset.add(&recver.publicrandomvec[ENCODING_PER_ELEMENT_BITS + ii]);
            }
        }

        for ii in 0..recver_result.0.len() {
            let el_bits = &recver_result.0[ii];
            let mut compressed_temp = vec![0u8; curve.fr_bytes];
            for jj in 0..curve.fr_bytes {
                compressed_temp[jj] = ((el_bits[jj * 8 + 0] as u8) << 0)
                    | ((el_bits[jj * 8 + 1] as u8) << 1)
                    | ((el_bits[jj * 8 + 2] as u8) << 2)
                    | ((el_bits[jj * 8 + 3] as u8) << 3)
                    | ((el_bits[jj * 8 + 4] as u8) << 4)
                    | ((el_bits[jj * 8 + 5] as u8) << 5)
                    | ((el_bits[jj * 8 + 6] as u8) << 6)
                    | ((el_bits[jj * 8 + 7] as u8) << 7);
            }
            let mut beta_temp = curve.parse_scalar(&compressed_temp);
            for jj in curve.fr_bits..(curve.fr_bits + ENCODING_PER_ELEMENT_BITS) {
                if recver_result.0[ii][jj] {
                    beta_temp = beta_temp.add(&recver.publicrandomvec[jj - curve.fr_bits]);
                }
            }
            assert!((beta_temp.add(&encoding_offset)) == beta[ii]);
        }

        child.join().unwrap();
    }

    #[test]
    fn test_mul_mul() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let mut alpha = Vec::with_capacity(10);
        let mut alpha_child = Vec::with_capacity(10);
        for ii in 0..10 {
            alpha.push(curve.rand_scalar(&mut rng));
            alpha_child.push(alpha[ii].clone());
        }

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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &ro.get_dyadic_tagger(1),
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let extensions = sender.mul_extend(10, &dro, r1[1].as_mut().unwrap());
            let mut results = Vec::with_capacity(10);
            for ii in 0..10 {
                results.push(
                    sender
                        .mul_transfer(
                            &[&alpha_child[ii]],
                            &[extensions.0[ii].clone()],
                            &extensions.1,
                            &dro,
                            &mut rng,
                            s1[1].as_mut().unwrap(),
                        )
                        .unwrap()[0]
                        .clone(),
                );
            }
            results
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(10);
        for _ in 0..10 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let extensions = recver
            .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
            .unwrap();
        let mut results = Vec::with_capacity(10);
        for ii in 0..10 {
            results.push(
                recver
                    .mul_transfer(
                        &[extensions.0[ii].clone()],
                        &extensions.1,
                        &[extensions.2[ii].clone()],
                        &extensions.3,
                        &dro,
                        r2[0].as_mut().unwrap(),
                    )
                    .unwrap()[0]
                    .clone(),
            );
        }

        let childresult = child.join().unwrap();
        for ii in 0..10 {
            assert_eq!(
                (results[ii].add(&childresult[ii])),
                beta[ii].mul(&alpha[ii])
            );
        }
    }

    #[test]
    fn test_mul_refresh() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let mut refresh_rand = [0u8; HASH_SIZE];
        rng.fill_bytes(&mut refresh_rand);
        let mut alpha = Vec::with_capacity(10);
        let mut alpha_child = Vec::with_capacity(10);
        for ii in 0..10 {
            alpha.push(curve.rand_scalar(&mut rng));
            alpha_child.push(alpha[ii].clone());
        }

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

            let dro = ro.get_dyadic_tagger(1);
            let mut sender = MulSender::new(
                curve,
                &ro.get_dyadic_tagger(1),
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            sender.apply_refresh(&refresh_rand, &dro).unwrap();
            let extensions = sender.mul_extend(10, &dro, r1[1].as_mut().unwrap());
            let mut results = Vec::with_capacity(10);
            for ii in 0..10 {
                results.push(
                    sender
                        .mul_transfer(
                            &[&alpha_child[ii]],
                            &[extensions.0[ii].clone()],
                            &extensions.1,
                            &dro,
                            &mut rng,
                            s1[1].as_mut().unwrap(),
                        )
                        .unwrap()[0]
                        .clone(),
                );
            }
            results
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let mut recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        recver.apply_refresh(&refresh_rand, &dro).unwrap();
        let mut beta = Vec::with_capacity(10);
        for _ in 0..10 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let extensions = recver
            .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
            .unwrap();
        let mut results = Vec::with_capacity(10);
        for ii in 0..10 {
            results.push(
                recver
                    .mul_transfer(
                        &[extensions.0[ii].clone()],
                        &extensions.1,
                        &[extensions.2[ii].clone()],
                        &extensions.3,
                        &dro,
                        r2[0].as_mut().unwrap(),
                    )
                    .unwrap()[0]
                    .clone(),
            );
        }

        let childresult = child.join().unwrap();
        for ii in 0..10 {
            assert_eq!(results[ii].add(&childresult[ii]), beta[ii].mul(&alpha[ii]));
        }
    }

    #[test]
    fn test_mul_batchmul() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let mut alpha = Vec::with_capacity(10);
        let mut alpha_child = Vec::with_capacity(10);
        for ii in 0..10 {
            alpha.push(curve.rand_scalar(&mut rng));
            alpha_child.push(alpha[ii].clone());
        }

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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &ro.get_dyadic_tagger(1),
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let extensions = sender.mul_extend(10, &dro, r1[1].as_mut().unwrap());
            let results = sender
                .mul_transfer(
                    &alpha_child.iter().collect::<Vec<_>>(),
                    &extensions.0,
                    &extensions.1,
                    &dro,
                    &mut rng,
                    s1[1].as_mut().unwrap(),
                )
                .unwrap();
            results
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(10);
        for _ in 0..10 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let extensions = recver
            .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
            .unwrap();
        let results = recver
            .mul_transfer(
                &extensions.0,
                &extensions.1,
                &extensions.2,
                &extensions.3,
                &dro,
                r2[0].as_mut().unwrap(),
            )
            .unwrap();

        let childresult = child.join().unwrap();
        for ii in 0..10 {
            assert_eq!(results[ii].add(&childresult[ii]), beta[ii].mul(&alpha[ii]));
        }
    }

    #[test]
    fn test_mul_rmul() {
        let curve = &P521;
        let mut rng = rand::thread_rng();

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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &dro,
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let extensions = sender
                .rmul_extend(10, &dro, &mut rng, r1[1].as_mut().unwrap())
                .unwrap();
            let mut results = Vec::with_capacity(10);
            for ii in 0..10 {
                results.push((
                    extensions.2[ii].clone(),
                    sender
                        .rmul_transfer(
                            &[&extensions.2[ii]],
                            &[extensions.0[ii].clone()],
                            &extensions.1,
                            &dro,
                            &mut rng,
                            s1[1].as_mut().unwrap(),
                        )
                        .unwrap()[0]
                        .clone(),
                ));
            }
            results
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(10);
        for _ in 0..10 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let extensions = recver
            .rmul_encode_and_extend(10, &dro, &mut rng, s2[0].as_mut().unwrap())
            .unwrap();
        let mut results = Vec::with_capacity(10);
        for ii in 0..10 {
            results.push(
                recver
                    .rmul_transfer(
                        &[extensions.0[ii].clone()],
                        &extensions.1,
                        &[extensions.2[ii].clone()],
                        &extensions.3,
                        &dro,
                        r2[0].as_mut().unwrap(),
                    )
                    .unwrap()[0]
                    .clone(),
            );
        }

        let childresult = child.join().unwrap();
        for ii in 0..10 {
            assert_eq!(
                results[ii].add(&childresult[ii].1),
                extensions.4[ii].mul(&childresult[ii].0)
            );
        }
    }

    #[test]
    fn test_mul_rbatchmul() {
        let curve = &P521;
        let mut rng = rand::thread_rng();

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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &dro,
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let extensions = sender
                .rmul_extend(10, &dro, &mut rng, r1[1].as_mut().unwrap())
                .unwrap();
            let results = sender
                .rmul_transfer(
                    &extensions.2.iter().collect::<Vec<_>>(),
                    &extensions.0,
                    &extensions.1,
                    &dro,
                    &mut rng,
                    s1[1].as_mut().unwrap(),
                )
                .unwrap();
            extensions
                .2
                .into_iter()
                .zip(results.into_iter())
                .collect::<Vec<_>>()
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(10);
        for _ in 0..10 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let extensions = recver
            .rmul_encode_and_extend(10, &dro, &mut rng, s2[0].as_mut().unwrap())
            .unwrap();
        let results = recver
            .rmul_transfer(
                &extensions.0,
                &extensions.1,
                &extensions.2,
                &extensions.3,
                &dro,
                r2[0].as_mut().unwrap(),
            )
            .unwrap();

        let childresult = child.join().unwrap();
        for ii in 0..10 {
            assert_eq!(
                results[ii].add(&childresult[ii].1),
                extensions.4[ii].mul(&childresult[ii].0)
            );
        }
    }

    #[test]
    fn test_mul_multimul() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let mut alpha = Vec::with_capacity(10);
        let mut alpha_child = Vec::with_capacity(10);
        for ii in 0..10 {
            alpha.push(curve.rand_scalar(&mut rng));
            alpha_child.push(alpha[ii].clone());
        }

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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &dro,
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let extensions = sender.mul_extend(1, &dro, r1[1].as_mut().unwrap());
            let mut results = Vec::with_capacity(10);
            for ii in 0..10 {
                results.push(
                    sender
                        .mul_transfer(
                            &[&alpha_child[ii]],
                            &[extensions.0[0].clone()],
                            &extensions.1,
                            &dro,
                            &mut rng,
                            s1[1].as_mut().unwrap(),
                        )
                        .unwrap()[0]
                        .clone(),
                );
            }
            results
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(1);
        beta.push(curve.rand_scalar(&mut rng));

        let extensions = recver
            .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
            .unwrap();
        let mut results = Vec::with_capacity(10);
        for _ in 0..10 {
            results.push(
                recver
                    .mul_transfer(
                        &[extensions.0[0].clone()],
                        &extensions.1,
                        &[extensions.2[0].clone()],
                        &extensions.3,
                        &dro,
                        r2[0].as_mut().unwrap(),
                    )
                    .unwrap()[0]
                    .clone(),
            );
        }

        let childresult = child.join().unwrap();
        for ii in 0..10 {
            assert_eq!(results[ii].add(&childresult[ii]), beta[0].mul(&alpha[ii]));
        }
    }

    #[bench]
    fn bench_mul_mul_extend(b: &mut Bencher) -> () {
        let curve = &P521;
        let mut rng = rand::thread_rng();
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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &dro,
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let mut keepgoing = [1u8; 1];
            r1[1].as_mut().unwrap().read_exact(&mut keepgoing).unwrap();
            while keepgoing[0] > 0 {
                sender.mul_extend(2, &dro, r1[1].as_mut().unwrap());
                r1[1].as_mut().unwrap().read_exact(&mut keepgoing).unwrap();
            }
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(2);
        for _ in 0..2 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let mut ii: usize = 0;
        b.iter(|| {
            s2[0].as_mut().unwrap().write(&[1]).unwrap();
            s2[0].as_mut().unwrap().flush().unwrap();
            recver
                .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
                .unwrap();
            ii += 1;
        });

        s2[0].as_mut().unwrap().write(&[0]).unwrap();
        s2[0].as_mut().unwrap().flush().unwrap();
        child.join().unwrap();
    }

    #[bench]
    fn bench_mul_mul_2_and_2(b: &mut Bencher) -> () {
        let curve = &P521;
        let mut rng = rand::thread_rng();
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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &dro,
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let mut keepgoing = [1u8; 1];

            let mut alpha = Vec::with_capacity(2);
            for _ in 0..2 {
                alpha.push(curve.rand_scalar(&mut rng));
            }

            r1[1].as_mut().unwrap().read_exact(&mut keepgoing).unwrap();
            while keepgoing[0] > 0 {
                let extensions = sender.mul_extend(2, &dro, r1[1].as_mut().unwrap());
                sender
                    .mul_transfer(
                        &[&alpha[0]],
                        &[extensions.0[0].clone()],
                        &extensions.1,
                        &dro,
                        &mut rng,
                        s1[1].as_mut().unwrap(),
                    )
                    .unwrap();
                sender
                    .mul_transfer(
                        &[&alpha[1]],
                        &[extensions.0[0].clone()],
                        &extensions.1,
                        &dro,
                        &mut rng,
                        s1[1].as_mut().unwrap(),
                    )
                    .unwrap();
                s1[1].as_mut().unwrap().flush().unwrap();
                r1[1].as_mut().unwrap().read_exact(&mut keepgoing).unwrap();
            }
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(2);
        for _ in 0..2 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        b.iter(|| {
            s2[0].as_mut().unwrap().write(&[1]).unwrap();
            s2[0].as_mut().unwrap().flush().unwrap();
            let extensions = recver
                .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
                .unwrap();
            recver
                .mul_transfer(
                    &[extensions.0[0].clone()],
                    &extensions.1,
                    &[extensions.2[0].clone()],
                    &extensions.3,
                    &dro,
                    r2[0].as_mut().unwrap(),
                )
                .unwrap();
            recver
                .mul_transfer(
                    &[extensions.0[0].clone()],
                    &extensions.1,
                    &[extensions.2[0].clone()],
                    &extensions.3,
                    &dro,
                    r2[0].as_mut().unwrap(),
                )
                .unwrap();
        });

        s2[0].as_mut().unwrap().write(&[0]).unwrap();
        s2[0].as_mut().unwrap().flush().unwrap();
        child.join().unwrap();
    }

    #[bench]
    fn bench_mul_mul_2_and_3(b: &mut Bencher) -> () {
        let curve = &P521;
        let mut rng = rand::thread_rng();
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

            let dro = ro.get_dyadic_tagger(1);
            let sender = MulSender::new(
                curve,
                &dro,
                &mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            );
            let mut keepgoing = [1u8; 1];

            let mut alpha = Vec::with_capacity(3);
            for _ in 0..3 {
                alpha.push(curve.rand_scalar(&mut rng));
            }

            r1[1].as_mut().unwrap().read_exact(&mut keepgoing).unwrap();
            while keepgoing[0] > 0 {
                let extensions = sender.mul_extend(2, &dro, r1[1].as_mut().unwrap());
                sender
                    .mul_transfer(
                        &[&alpha[0]],
                        &[extensions.0[0].clone()],
                        &extensions.1,
                        &dro,
                        &mut rng,
                        s1[1].as_mut().unwrap(),
                    )
                    .unwrap();
                sender
                    .mul_transfer(
                        &[&alpha[1]],
                        &[extensions.0[0].clone()],
                        &extensions.1,
                        &dro,
                        &mut rng,
                        s1[1].as_mut().unwrap(),
                    )
                    .unwrap();
                sender
                    .mul_transfer(
                        &[&alpha[2]],
                        &[extensions.0[1].clone()],
                        &extensions.1,
                        &dro,
                        &mut rng,
                        s1[1].as_mut().unwrap(),
                    )
                    .unwrap();
                s1[1].as_mut().unwrap().flush().unwrap();
                r1[1].as_mut().unwrap().read_exact(&mut keepgoing).unwrap();
            }
        });

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

        let dro = ro.get_dyadic_tagger(0);
        let recver = MulRecver::new(
            curve,
            &dro,
            &mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();
        let mut beta = Vec::with_capacity(2);
        for _ in 0..2 {
            beta.push(curve.rand_scalar(&mut rng));
        }

        let mut ii: usize = 0;
        b.iter(|| {
            s2[0].as_mut().unwrap().write(&[1]).unwrap();
            s2[0].as_mut().unwrap().flush().unwrap();
            let extensions = recver
                .mul_encode_and_extend(&beta, &dro, &mut rng, s2[0].as_mut().unwrap())
                .unwrap();
            recver
                .mul_transfer(
                    &[extensions.0[0].clone()],
                    &extensions.1,
                    &[extensions.2[0].clone()],
                    &extensions.3,
                    &dro,
                    r2[0].as_mut().unwrap(),
                )
                .unwrap();
            recver
                .mul_transfer(
                    &[extensions.0[0].clone()],
                    &extensions.1,
                    &[extensions.2[0].clone()],
                    &extensions.3,
                    &dro,
                    r2[0].as_mut().unwrap(),
                )
                .unwrap();
            recver
                .mul_transfer(
                    &[extensions.0[1].clone()],
                    &extensions.1,
                    &[extensions.2[1].clone()],
                    &extensions.3,
                    &dro,
                    r2[0].as_mut().unwrap(),
                )
                .unwrap();
            ii += 1;
        });

        s2[0].as_mut().unwrap().write(&[0]).unwrap();
        s2[0].as_mut().unwrap().flush().unwrap();
        child.join().unwrap();
    }
}
