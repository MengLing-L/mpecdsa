/***********
 * This module implements the VSOT Random Oblivious Transfer Protocol,
 * as described in the paper "Secure Two-party Threshold ECDSA from ECDSA Assumptions"
 * by Doerner, Kondi, Lee, and shelat (https://eprint.iacr.org/2018/499)
 *
 * VSOT is based upon the Simplest Protocol for Oblivious Transfer
 * as described in the paper "The Simplest Protocol For Oblivious Transfer"
 * by Chou and Orlandi (https://eprint.iacr.org/2015/267)
 ***********/

use std::io::prelude::*;

//use byteorder::{ByteOrder, LittleEndian};

use rand::Rng;

use crate::utils::Curve;
use crate::utils::Point;
use crate::utils::Scalar;

use super::ro::*;
use super::zkpok::*;
use super::*;
use std::error::Error;

#[derive(Clone)]
pub struct ROTSender {
    curve: &'static Curve,
    sk: Scalar,
    pk_negsquared: Point,
}

impl ROTSender {
    pub fn new<T: Write, R: Rng>(
        curve: &'static Curve,
        ro: &DyadicROTagger,
		rng: &mut R,
        send: &mut T,
    ) -> Result<ROTSender, Box<dyn Error>> {
        let (sk, pk) = curve.rand_scalar_and_point(rng);

        let buf = pk.to_bytes();
        send.write(&buf)?;
        let mro = ModelessDyadicROTagger::new(&ro, true);
        zkpok::prove_dl_fs(curve, &sk, &pk, &mro, rng, send)?;

        Ok(ROTSender {
            curve,
            pk_negsquared: Point::from_scalar(curve, &sk.sqr()).neg(),
            sk,
        })
    }

    pub fn decode<T: Read>(
        &mut self,
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> io::Result<(Vec<u8>, Vec<u8>)> {
        let ga_select = Point::from_reader(self.curve, recv);
        let msg_0 = ga_select.mul(&self.sk);
        let msg_1 = msg_0.add(&self.pk_negsquared);

        let ro_tag = ro.next_dyadic_tag();

        Ok((
            hash(&[ro_tag.clone(), msg_0.to_bytes()].concat()),
            hash(&[ro_tag, msg_1.to_bytes()].concat()),
        ))
    }
}

#[derive(Clone)]
pub struct ROTRecver {
    curve: &'static Curve,
    pk: Point,
}

impl ROTRecver {
    pub fn new<T: Read>(
        curve: &'static Curve,
        ro: &DyadicROTagger,
        recv: &mut T,
    ) -> Result<ROTRecver, Box<dyn Error>> {
        let pk = Point::from_reader(curve, recv);
        let mro = ModelessDyadicROTagger::new(&ro, true);
        assert!(verify_dl_fs(curve, &pk, &mro, recv));
        Ok(ROTRecver {
            curve: curve,
            pk: pk,
        })
    }

    pub fn choose<T: Write, R: Rng>(
        &mut self,
        choice_bit: bool,
        ro: &DyadicROTagger,
		rng: &mut R,
        send: &mut T,
    ) -> io::Result<Vec<u8>> {
        let (a, ga_choice0) = self.curve.rand_scalar_and_point(rng);
        let ga_choice1 = ga_choice0.add(&self.pk); //always do this to avoid timing channel
        let pka = self.pk.mul(&a);

        send.write(&if choice_bit {
            ga_choice1.to_bytes()
        } else {
            ga_choice0.to_bytes()
        })?;

        Ok(hash(&[ro.next_dyadic_tag(), pka.to_bytes()].concat()))
    }
}

#[derive(Clone)]
pub struct ROTSendVerifier {
    msg_0_com: Vec<u8>,
    msg_1_com: Vec<u8>,
    exp_chal: Vec<u8>,
}

impl ROTSendVerifier {
    pub fn new<T: Write>(
        msg_0: Vec<u8>,
        msg_1: Vec<u8>,
        ro: &DyadicROTagger,
        send: &mut T,
    ) -> Result<ROTSendVerifier, Box<dyn Error>> {
        let mut s = ROTSendVerifier {
            msg_0_com: vec![],
            msg_1_com: vec![],
            exp_chal: vec![],
        };

        let ro_tag_1 = ro.next_dyadic_tag();
        let ro_tag_2 = ro.next_dyadic_tag();
        s.msg_0_com = hash(&[ro_tag_1.clone(), msg_0].concat());
        s.msg_1_com = hash(&[ro_tag_1, msg_1].concat());

        s.exp_chal = hash(&[ro_tag_2.clone(), s.msg_0_com.clone()].concat());
        let mut com_msg = hash(&[ro_tag_2, s.msg_1_com.clone()].concat());

        for ii in 0..com_msg.len() {
            com_msg[ii] ^= s.exp_chal[ii];
        }
        send.write(&com_msg)?;

        Ok(s)
    }

    pub fn open<T1: Read, T2: Write>(
        &self,
        recv: &mut T1,
        send: &mut T2,
    ) -> Result<(), Box<dyn Error>> {
        let mut chal_msg = vec![0u8; HASH_SIZE];
        recv.read_exact(&mut chal_msg)?;

        assert_eq!(chal_msg, self.exp_chal);
        send.write(&self.msg_0_com)?;
        send.write(&self.msg_1_com)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct ROTRecvVerifier {
    choice_bit: bool,
    hashed_chosen_msg: Vec<u8>,
    com_msg: Vec<u8>,
    tag2: Vec<u8>,
}

impl ROTRecvVerifier {
    pub fn new<T1: Read, T2: Write>(
        msg: Vec<u8>,
        choice_bit: bool,
        ro: &DyadicROTagger,
        recv: &mut T1,
        send: &mut T2,
    ) -> Result<ROTRecvVerifier, Box<dyn Error>> {
        let mut s = ROTRecvVerifier {
            choice_bit: choice_bit,
            hashed_chosen_msg: vec![],
            com_msg: vec![0u8; HASH_SIZE],
            tag2: vec![],
        };

        s.hashed_chosen_msg = hash(&[ro.next_dyadic_tag(), msg].concat());

        s.tag2 = ro.next_dyadic_tag();
        let mut chal_msg = hash(&[s.tag2.clone(), s.hashed_chosen_msg.clone()].concat());

        recv.read_exact(&mut s.com_msg)?;

        if choice_bit {
            for ii in 0..chal_msg.len() {
                chal_msg[ii] ^= s.com_msg[ii];
            }
        }
        send.write(&chal_msg)?;
        Ok(s)
    }

    pub fn open<T: Read>(&mut self, recv: &mut T) -> Result<(), Box<dyn Error>> {
        let mut msg_0_com = vec![0u8; HASH_SIZE];
        let mut msg_1_com = vec![0u8; HASH_SIZE];
        recv.read_exact(&mut msg_0_com)?;
        recv.read_exact(&mut msg_1_com)?;
        let exp_com_msg = hash(&[self.tag2.clone(), msg_0_com.clone()].concat());
        for ii in 0..exp_com_msg.len() {
            self.com_msg[ii] ^= exp_com_msg[ii];
        }

        let exp_com_msg = hash(&[self.tag2.clone(), msg_1_com.clone()].concat());

        assert_eq!(exp_com_msg, self.com_msg);
        assert_eq!(
            &if self.choice_bit {
                msg_1_com
            } else {
                msg_0_com
            },
            &self.hashed_chosen_msg
        );

        Ok(())
    }
}

// for convenience:
pub fn rot_send_batch<T1: Read, T2: Write, R: Rng>(
    curve: &'static Curve,
    count: usize,
    ro: &DyadicROTagger,
	rng: &mut R,
    recv: &mut T1,
    send: &mut T2,
) -> Result<Vec<(Vec<u8>, Vec<u8>)>, Box<dyn Error>> {
    let mut rotsender = ROTSender::new(curve, ro, rng, send)?;
    send.flush()?;

    let mut sender_msgs: Vec<(Vec<u8>, Vec<u8>)> = Vec::with_capacity(count);
    let mut sverifiers: Vec<ROTSendVerifier> = Vec::with_capacity(count);
    for _ in 0..count {
        let (sender_msg_0, sender_msg_1) = rotsender.decode(ro, recv)?;
        sender_msgs.push((sender_msg_0, sender_msg_1));
    }
    for ii in 0..count {
        sverifiers.push(ROTSendVerifier::new(
            sender_msgs[ii].0.clone(),
            sender_msgs[ii].1.clone(),
            ro,
            send,
        )?);
    }
    send.flush()?;

    for ii in 0..count {
        sverifiers[ii].open(recv, send)?;
    }
    send.flush()?;

    Ok(sender_msgs)
}

pub fn rot_recv_batch<T1: Read, T2: Write, R: Rng>(
    curve: &'static Curve,
    choice_bits: &[bool],
    ro: &DyadicROTagger,
	rng: &mut R,
    recv: &mut T1,
    send: &mut T2,
) -> Result<Vec<Vec<u8>>, Box<dyn Error>> {
    let mut rotrecver = ROTRecver::new(curve, ro, recv)?;

    let mut recver_msgs: Vec<Vec<u8>> = Vec::with_capacity(choice_bits.len());
    for ii in 0..choice_bits.len() {
        recver_msgs.push(rotrecver.choose(choice_bits[ii], ro, rng, send)?);
    }
    send.flush()?;

    let mut rverifiers: Vec<ROTRecvVerifier> = Vec::with_capacity(choice_bits.len());
    for ii in 0..choice_bits.len() {
        rverifiers.push(ROTRecvVerifier::new(
            recver_msgs[ii].clone(),
            choice_bits[ii],
            ro,
            recv,
            send,
        )?);
    }
    send.flush()?;

    for ii in 0..choice_bits.len() {
        rverifiers[ii].open(recv)?;
    }

    Ok(recver_msgs)
}

#[cfg(test)]
mod tests {
    use crate::utils::P521;

    use super::channelstream::*;
    use super::*;
    use std::thread;
    use rand::Rng;
    use test::Bencher;

    const N: usize = 128;

    #[test]
    fn test_rot() {
        let curve = &P521;
        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(2);

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let mut rng = rand::thread_rng();

        let mut choice_bits: [bool; N] = [false; N];
        for ii in 0..choice_bits.len() {
            choice_bits[ii] = rng.gen();
        }

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
            rot_send_batch(
                curve,
                N,
                &mut ro.get_dyadic_tagger(1),
				&mut rng,
                r1[1].as_mut().unwrap(),
                s1[1].as_mut().unwrap(),
            )
            .unwrap();
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
        rot_recv_batch(
            curve,
            &choice_bits,
            &mut ro.get_dyadic_tagger(0),
			&mut rng,
            r2[0].as_mut().unwrap(),
            s2[0].as_mut().unwrap(),
        )
        .unwrap();

        child.join().unwrap();
    }

    #[bench]
    fn bench_rot_batch(b: &mut Bencher) {
        let curve = &P521;
        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(2);

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let mut rng = rand::thread_rng();

        let mut choice_bits: [bool; N] = [false; N];
        for ii in 0..choice_bits.len() {
            choice_bits[ii] = rng.gen();
        }

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

            let mut keepgoing = [1u8; 1];
            r1[1]
                .as_mut()
                .unwrap()
                .read_exact(&mut keepgoing)
                .expect("Sender failed to read (1)");
            while keepgoing[0] > 0 {
                rot_send_batch(
                    curve,
                    N,
                    &mut ro.get_dyadic_tagger(1),
					&mut rng,
                    r1[1].as_mut().unwrap(),
                    s1[1].as_mut().unwrap(),
                )
                .unwrap();
                r1[1]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut keepgoing)
                    .expect("Sender failed to read (2)");
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

        b.iter(|| {
            s2[0]
                .as_mut()
                .unwrap()
                .write(&[1])
                .expect("Recver failed to write (1)");
            s2[0]
                .as_mut()
                .unwrap()
                .flush()
                .expect("Recver failed to flush");
            rot_recv_batch(
                curve,
                &choice_bits,
                &mut ro.get_dyadic_tagger(0),
				&mut rng,
                r2[0].as_mut().unwrap(),
                s2[0].as_mut().unwrap(),
            )
            .unwrap();
        });

        s2[0]
            .as_mut()
            .unwrap()
            .write(&[0])
            .expect("Recver failed to write (2)");
        s2[0]
            .as_mut()
            .unwrap()
            .flush()
            .expect("Recver failed to flush");
        child.join().unwrap();
    }
}
