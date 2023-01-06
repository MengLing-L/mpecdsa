/***********
 * This module implements the two-party ECDSA protocols
 * described in the paper "Secure Two-party Threshold ECDSA from ECDSA Assumptions"
 * by Doerner, Kondi, Lee, and shelat (https://eprint.iacr.org/2018/499)
 *
 * It also implements the multi-party ECDSA protocols
 * described in the paper "Threshold ECDSA from ECDSA Assumptions"
 * by Doerner, Kondi, Lee, and shelat
 ***********/

use std::io::prelude::*;
use std::io::{BufWriter, Cursor};

use byteorder::{ByteOrder, LittleEndian};

use rand::rngs::ThreadRng;
use rand::{Rng, SeedableRng};

use rand_chacha::ChaChaRng;
use rayon::prelude::*;

use crate::utils::{Curve, Point, Scalar};

use super::mpmul::*;
use super::mul::*;
use super::ro::*;
use super::zkpok::*;
use super::*;
use std::error::Error;

pub fn ecdsa_verify(curve: &'static Curve, msg: &[u8], sig: (Scalar, Scalar), pk: Point) -> bool {
    let r = sig.0;
    let s = sig.1;

    if r == Scalar::zero(curve) || s == Scalar::zero(curve) {
        return false;
    }

    // r,s are in range [1,order-1]
    // z = hash(msg)
    let mut z = hash(msg);
    let z = Scalar::from_bytes(curve, &z);

    // w = s^{-1}
    // u1 = zw mod n
    // u2 = rw mod n
    let w = s.inv();
    let u1 = z.mul(&w);
    let u2 = r.mul(&w);

    // p = g^u1 * pk^u2
    // check p.x == r
    let p = Point::add(&pk.mul(&u2), &Point::from_scalar(curve, &u1));
    let mut pb = p.x_bytes();
    let px = Scalar::from_bytes(curve, &pb[..]);
    if px == r {
        return true;
    }

    return false;
}

//#[derive(Clone)]
pub struct Alice2P {
    ro: GroupROTagger,
    multiplier: mul::MulSender,
    ska: Scalar,
    #[allow(dead_code)]
    pk: Point,
    curve: &'static Curve,
}

//#[derive(Clone)]
pub struct Bob2P {
    ro: GroupROTagger,
    multiplier: mul::MulRecver,
    skb: Scalar,
    #[allow(dead_code)]
    pk: Point,
    curve: &'static Curve,
}

pub struct ThresholdSigner {
    playerindex: usize,
    threshold: usize,
    ro: GroupROTagger,
    multiplier: Vec<mul::MulPlayer>,
    poly_point: Scalar,
    #[allow(dead_code)]
    pk: Point,
    curve: &'static Curve,
}

pub type ProactiveRefreshPackage = (Point, Vec<u8>, Scalar, Point, Scalar);

impl Alice2P {
    pub fn new<TR: Read, TW: Write, R: Rng>(
        curve: &'static Curve,
        ska: &Scalar,
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<Self, Box<dyn Error>> {
        let secp_bytes = curve.fq_bytes * 2 + 1;
        let fr_bytes = curve.fr_bytes;
        let ro = GroupROTagger::from_network_unverified(
            0,
            rng,
            &mut [None, Some(recv)],
            &mut [None, Some(send)],
        );

        // commit to PoK-DL for pk_a
        let pka = Point::from_scalar(curve, ska);
        let (proofcommitment, proof) = prove_dl_fs_to_com(
            curve,
            ska,
            &pka,
            &ModelessGroupROTagger::new(&ro, false),
			rng,
        )?;
        send.write(&proofcommitment)?;
        send.flush()?;

        // recv pk_b
        let mut buf = vec![0u8; secp_bytes];
        recv.read_exact(&mut buf)?;
        let pkb = Point::from_bytes(curve, &buf);

        // verify PoK-DL for pk_b
        assert!(verify_dl_fs(
            curve,
            &pkb,
            &ModelessDyadicROTagger::new(&ro.get_dyadic_tagger(1), false),
            recv
        ));

        // send pk_a
        // open commitment to PoK-DL
        buf = pka.to_bytes();
        send.write(&buf)?;
        send.write(&proof)?;
        send.flush()?;

        // initialize multiplication
        let mul = mul::MulSender::new(curve, &ro.get_dyadic_tagger(1), rng, recv, send);

        // calc pk, setup OT exts
        let pk = pkb.mul(&ska);
        let res = Alice2P {
            ro: ro,
            multiplier: mul,
            ska: ska.clone(),
            pk: pk,
            curve,
        };

        Ok(res)
    }

    pub fn sign<TR: Read, TW: Write + Send, R: Rng>(
        &self,
        msg: &[u8],
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<(), Box<dyn Error>> {
        let secp_bytes = self.curve.fq_bytes * 2 + 1;
        let fr_bytes = self.curve.fr_bytes;
        let mut bufsend = BufWriter::new(send);

        // precompute things you won't need till later

        // alice's instance key is of a special form for the two round version:
        // k_a = H(k'_a*G)+k'_a
        // this prevents her from choosing the value conveniently
        let kaprime = self.curve.rand_scalar(rng);
        let kapad = self.curve.rand_scalar(rng);

        // hash the message
        let z = Scalar::from_bytes(self.curve, &hash(msg));

        // online phase
        let dro = self.ro.get_dyadic_tagger(1);

        // recv D_b from bob
        let mut dbraw = vec![0u8; secp_bytes];
        recv.read_exact(&mut dbraw)?;
        let db = Point::from_bytes(self.curve, &dbraw);

        let rprime = db.mul(&kaprime);
        let mut rprimeraw = [dro.next_dyadic_tag(), rprime.to_bytes()].concat();
        let mut kaoffsetraw = hash(&rprimeraw);
        let kaoffset = Scalar::from_bytes(self.curve, &kaoffsetraw);
        let ka = kaoffset.add(&kaprime);

        let kai = ka.inv();
        let skai = kai.mul(&self.ska);

        // compute R = k_a*k_b*G, and get the x coordinate
        // do this early to save time later and give bob a chance to start the extensions
        let r = db.mul(&ka);
        let mut rxb = r.x_bytes();
        let rx = Scalar::from_bytes(self.curve, &rxb);
        let kapadda = Point::from_scalar(self.curve, &ka.mul(&kapad));

        // Prove knowledge of ka for R; hardcoded fiat-shamir so we can do preprocessing
        let kaproof_randcommitted = self.curve.rand_scalar(rng);
        let kaproof_randcommitment = db.mul(&kaproof_randcommitted);
        let mut kaproof_buf = [
            dro.next_dyadic_tag(),
            r.to_bytes(),
            kaproof_randcommitment.to_bytes(),
        ]
        .concat();
        let mut kaproof_challenge = hash(&kaproof_buf);
        let kaproof_challenge = Scalar::from_bytes(self.curve, &kaproof_challenge[..]);
        let kaproof_z = ka.mul(&kaproof_challenge).add(&kaproof_randcommitted);
        kaproof_buf.extend_from_slice(&kaproof_z.to_bytes());

        // generate OT extensions for two multiplications (input independent for alice)
        let extensions = self.multiplier.mul_extend(2, &dro, recv);

        // end first message (bob to alice)

        // alice sends D'_a = k'_a*G rather than D_a so that bob can check her work
        // she also sends her proof of knowledge for k_a
        bufsend.write(&rprimeraw[RO_TAG_SIZE..])?;
        bufsend.write(&kaproof_buf[(secp_bytes + RO_TAG_SIZE)..])?;
        bufsend.flush()?;

        // perform two multiplications with 1/k_a and sk_a/k_a.
        let t1a = self.multiplier.mul_transfer(
            &[&kai.add(&kapad)],
            &[extensions.0[0].clone()],
            &extensions.1,
            &dro,
            rng,
            &mut bufsend,
        )?[0]
            .clone();
        bufsend.flush()?;
        let mut gamma1raw = dro.next_dyadic_tag();
        let t2a = self.multiplier.mul_transfer(
            &[&skai],
            &[extensions.0[1].clone()],
            &extensions.1,
            &dro,
            rng,
            &mut bufsend,
        )?[0]
            .clone();
        bufsend.flush()?;

        // compute check value Gamma_1 for alice
        let gamma1 = r.mul(&t1a.neg()).add(&kapadda).add(&Point::gen(self.curve));
        gamma1raw.extend_from_slice(&gamma1.to_bytes());
        let mut enckey = hash(&gamma1raw);
        let mut kapadraw = kapad.to_bytes();
        for ii in 0..fr_bytes {
            kapadraw[ii] ^= enckey[ii];
        }
        bufsend.write(&kapadraw)?;
        bufsend.flush()?;

        // compute signature share m_a for alice
        let mut ma = t1a.mul(&z).add(&t2a.mul(&rx)).to_bytes();

        // compute check value Gamma_2, and encrypt m_a with H(Gamma_2)
        let t2ag = Point::from_scalar(self.curve, &t2a.neg());
        let t1apk = self.pk.mul(&t1a);
        let gamma2 = t2ag.add(&t1apk);
        let gamma2raw = [dro.next_dyadic_tag(), gamma2.to_bytes()].concat();
        enckey = hash(&gamma2raw);
        for ii in 0..fr_bytes {
            ma[ii] ^= enckey[ii];
        }

        // send encrypted signature share
        bufsend.write(&ma)?;
        bufsend.flush()?;

        // end second message (alice to bob)

        Ok(())
    }
}

impl Bob2P {
    pub fn new<TR: Read, TW: Write, R: Rng>(
        curve: &'static Curve,
        skb: &Scalar,
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<Self, Box<dyn Error>> {
        let ro = GroupROTagger::from_network_unverified(
            1,
            rng,
            &mut [Some(recv), None],
            &mut [Some(send), None],
        );

        // recv PoK commitment
        let mut proofcommitment = [0u8; HASH_SIZE];
        recv.read_exact(&mut proofcommitment)?;

        // send pk_b
        let pkb = Point::from_scalar(curve, skb);
        let mut buf = pkb.to_bytes();
        send.write(&buf)?;
        send.flush()?;

        // prove dl for pk_b
        prove_dl_fs(
            curve,
            &skb,
            &pkb,
            &ModelessGroupROTagger::new(&ro, false),
			rng,
            send,
        )?;

        // recv pk_a
        recv.read_exact(&mut buf)?;
		let pka = Point::from_bytes(curve, &buf);

        assert!(verify_dl_fs_with_com(
            curve,
            &pka,
            &proofcommitment,
            &ModelessDyadicROTagger::new(&ro.get_dyadic_tagger(0), false),
            recv
        )?);

        // initialize multiplication
        let mul = mul::MulRecver::new(curve, &ro.get_dyadic_tagger(0), rng, recv, send)?;

        // verify PoK to which alice previously committed, then calc pk, setup OT exts
        let pk = pka.mul(&skb);
        let res = Bob2P {
            ro: ro,
            multiplier: mul,
            skb: skb.clone(),
            pk: pk,
            curve,
        };

        Ok(res)
    }

    pub fn sign<TR: Read, TW: Write, R: Rng>(
        &self,
        msg: &[u8],
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<(Scalar, Scalar), Box<dyn Error>> {
        let secp_bytes = self.curve.fq_bytes * 2 + 1;
        let fr_bytes = self.curve.fr_bytes;
        let mut bufsend = BufWriter::new(send);

        // no precomputation - we want to begin writing as soon as possible

        // choose k_b, calc D_b = k_b*G, send D_b
        let (kb, db) = self.curve.rand_scalar_and_point(rng);
        let mut dbraw = db.to_bytes();
        bufsend.write(&dbraw)?;
        bufsend.flush()?;

        let dro = self.ro.get_dyadic_tagger(0);
        let rprime_tag = dro.next_dyadic_tag();
        let kaproof_tag = dro.next_dyadic_tag();

        // generate OT extensions for multiplications with 1/k_b and sk_b/k_b
        let kbi = kb.inv();
        let skbi = kbi.mul(&self.skb);
        let betas = [kbi.clone(), skbi.clone()];
        let extensions = self
            .multiplier
            .mul_encode_and_extend(&betas, &dro, rng, &mut bufsend)?;
        bufsend.flush()?;

        // end first message (bob to alice)

        // receive D'_a from alice, calculate D_a as D_a = H(D'_a)*G + D'_a
        let mut rprimeraw = vec![0u8; secp_bytes + RO_TAG_SIZE];
        recv.read_exact(&mut rprimeraw[RO_TAG_SIZE..])?;
        let rprime = Point::from_bytes(self.curve, &rprimeraw[RO_TAG_SIZE..]);
        rprimeraw[0..RO_TAG_SIZE].copy_from_slice(&rprime_tag);
        let mut kaoffsetraw = hash(&rprimeraw);
        let kaoffset = Scalar::from_bytes(self.curve, &kaoffsetraw);
        let kbkaoffsetg = Point::from_scalar(self.curve, &kb.mul(&kaoffset));

        // compute R = k_a*k_b*G, and get the x coordinate
        let r = kbkaoffsetg.add(&rprime);
        let mut rxb = r.x_bytes();
        let rx = Scalar::from_bytes(self.curve, &rxb);

        // verify alice's PoK of k_a for R
        let mut kaproof_buf = vec![0u8; 2 * secp_bytes + fr_bytes + RO_TAG_SIZE];
        kaproof_buf[RO_TAG_SIZE..(secp_bytes + RO_TAG_SIZE)].copy_from_slice(&r.to_bytes());
        recv.read_exact(&mut kaproof_buf[(RO_TAG_SIZE + secp_bytes)..])?;
        let kaproof_randcommitment = Point::from_bytes(
            self.curve,
            &kaproof_buf[(RO_TAG_SIZE + secp_bytes)..(2 * secp_bytes + RO_TAG_SIZE)],
        );
        let kaproof_z =
            Scalar::from_bytes(self.curve, &kaproof_buf[(RO_TAG_SIZE + 2 * secp_bytes)..]);
        kaproof_buf[0..RO_TAG_SIZE].copy_from_slice(&kaproof_tag);
        let mut kaproof_challenge = hash(&kaproof_buf[0..(2 * secp_bytes + RO_TAG_SIZE)]);
        let kaproof_challenge = Scalar::from_bytes(self.curve, &kaproof_challenge[..]);
        let kaproof_lhs = r.mul(&kaproof_challenge).add(&kaproof_randcommitment);
        let kaproof_rhs = Point::from_scalar(self.curve, &kaproof_z.mul(&kb));
        assert_eq!(kaproof_lhs, kaproof_rhs);

        // hash message
        let z = Scalar::from_bytes(self.curve, &hash(msg));

        // perform multiplications using the extensions we just generated
        let t1b = self.multiplier.mul_transfer(
            &[extensions.0[0].clone()],
            &extensions.1,
            &[extensions.2[0].clone()],
            &extensions.3,
            &dro,
            recv,
        )?[0]
            .clone();
        let gamma1 = r.mul(&t1b); // start calculating gamma_b early, to give the sender extra time
        let gamma1raw = [dro.next_dyadic_tag(), gamma1.to_bytes()].concat();
        let mut enckey = hash(&gamma1raw);
        let t2b = self.multiplier.mul_transfer(
            &[extensions.0[1].clone()],
            &extensions.1,
            &[extensions.2[1].clone()],
            &extensions.3,
            &dro,
            recv,
        )?[0]
            .clone();

        // compute the first check messages Gamma_1, and decrypt the pad
        let mut kapadraw = vec![0u8; fr_bytes];
        recv.read_exact(&mut kapadraw)?;
        for ii in 0..fr_bytes {
            kapadraw[ii] ^= enckey[ii];
        }
        let kapad = Scalar::from_bytes(self.curve, &kapadraw);

        let t1baug = t1b.sub(&kbi.mul(&kapad));
        let t2bg = Point::from_scalar(self.curve, &t2b);
        let t1bpk = self.pk.mul(&t1baug.neg());
        let gamma2 = t2bg.add(&t1bpk);
        let gamma2raw = [dro.next_dyadic_tag(), gamma2.to_bytes()].concat();
        let mut enckey = hash(&gamma2raw);

        // compute bob's signature share m_b
        let m_b = t1baug.mul(&z).add(&t2b.mul(&rx));

        // receive alice's signature share m_a, and decrypt using expected key
        let mut ma = vec![0u8; fr_bytes];
        recv.read_exact(&mut ma)?;
        for ii in 0..fr_bytes {
            ma[ii] ^= enckey[ii];
        }
        let m_a = Scalar::from_bytes(self.curve, &ma);

        // reconstruct signature
        let s = m_a.add(&m_b);

        // end second message (alice to bob)

        // verify signature. Abort if it's incorrect.
        assert!(ecdsa_verify(
            self.curve,
            msg,
            (rx.clone(), s.clone()),
            self.pk.clone()
        ));
        Ok((rx, s))
    }
}

impl ThresholdSigner {
    pub fn new<TR: Read + Send, TW: Write + Send, R: Rng>(
        curve: &'static Curve,
        playerindex: usize,
        threshold: usize,
        rng: &mut R,
        recv: &mut [Option<TR>],
        send: &mut [Option<TW>],
    ) -> Result<Self, Box<dyn Error>> {
        let secp_bytes = curve.fq_bytes * 2 + 1;
        let fr_bytes = curve.fr_bytes;
        assert_eq!(recv.len(), send.len());
        let playercount = recv.len();

        let ro = {
            let mut prunedrecv: Vec<Option<&mut TR>> =
                recv.iter_mut().map(|val| val.as_mut()).collect();
            let mut prunedsend: Vec<Option<&mut TW>> =
                send.iter_mut().map(|val| val.as_mut()).collect();
            GroupROTagger::from_network_unverified(
                playerindex,
                rng,
                &mut prunedrecv[..],
                &mut prunedsend[..],
            )
        };

        let sk_frag = curve.rand_scalar(rng);

        // Random polynomial for shamir secret sharing.
        // This polynomial represents my secret; we will sum all the polynomials later to sum the secret.
        // Note that we generate k-1 coefficients; the last is the secret
        let mut coefficients: Vec<Scalar> = Vec::with_capacity(threshold);
        coefficients.push(sk_frag.clone());
        for _ in 1..threshold {
            coefficients.push(curve.rand_scalar(rng));
        }

        // poly_point will later be my point on the shared/summed polynomial. Create it early
        // so that the component from my own individual polynomial can be added.
        let mut poly_point = Scalar::zero(curve);
        // evaluate my polynomial once for each player, and send everyone else their fragment
        for ii in 0..playercount {
            let mut poly_frag = coefficients[coefficients.len() - 1].clone();
            for jj in (0..(coefficients.len() - 1)).rev() {
                poly_frag = poly_frag
                    .mul(&Scalar::from_u32(curve, (ii + 1) as u32))
                    .add(&coefficients[jj]);
            }
            if ii == playerindex {
                poly_point = poly_frag;
            } else {
                let mut poly_frag_raw = poly_frag.to_bytes();
                send[ii].as_mut().unwrap().write(&poly_frag_raw)?;
                send[ii].as_mut().unwrap().flush()?;
            }
        }

        // recieve polynomial fragments from each player, and sum them to find my point on the shared/summed polynomial
        for ii in 0..playercount {
            if ii != playerindex {
                let mut poly_frag_raw = vec![0u8; fr_bytes];
                recv[ii].as_mut().unwrap().read_exact(&mut poly_frag_raw)?;
                let poly_frag = Scalar::from_bytes(curve, &poly_frag_raw);
                poly_point = poly_point.add(&poly_frag);
            }
        }

        let mut points_com = Vec::with_capacity(playercount);
        let mut pk = Point::inf(curve);

        if threshold >= playercount / 2 {
            // calculate p(playerindex)*G, an EC point with my polynomial point in the exponent, and broadcast it to everyone
            // in the dishonest majority case, we also need a PoK
            let point_com = Point::from_scalar(curve, &poly_point);
            let (proofcommitment, proof) = prove_dl_fs_to_com(
                curve,
                &poly_point,
                &point_com,
                &ModelessGroupROTagger::new(&ro, false),
				rng
			)?;
            for ii in 0..playercount {
                if ii != playerindex {
                    send[ii].as_mut().unwrap().write(&proofcommitment)?;
                    send[ii].as_mut().unwrap().flush()?;
                }
            }
            // now collect everyone else's commitments
            let mut othercommitments = vec![[0u8; HASH_SIZE]; playercount];
            for ii in 0..playercount {
                if ii != playerindex {
                    recv[ii]
                        .as_mut()
                        .unwrap()
                        .read_exact(&mut othercommitments[ii])?;
                }
            }
            // when all commitments are in, release the proof
            let mut point_com_raw = point_com.to_bytes();
            for ii in 0..playercount {
                if ii != playerindex {
                    send[ii].as_mut().unwrap().write(&point_com_raw)?;
                    send[ii].as_mut().unwrap().write(&proof)?;
                    send[ii].as_mut().unwrap().flush()?;
                }
            }
            // and finally verify that the proofs are valid
            for ii in 0..playercount {
                if ii == playerindex {
                    points_com.push(point_com.clone());
                } else {
                    recv[ii].as_mut().unwrap().read_exact(&mut point_com_raw)?;
                    let this_point_com = Point::from_bytes(curve, &point_com_raw);
                    assert!(verify_dl_fs_with_com(
                        curve,
                        &this_point_com,
                        &othercommitments[ii],
                        &ModelessDyadicROTagger::new(&ro.get_dyadic_tagger(ii), false),
                        &mut recv[ii].as_mut().unwrap()
                    )?);
                    points_com.push(this_point_com);
                }
            }
        } else {
            // calculate p(playerindex)*G, an EC point with my polynomial point in the exponent, and broadcast it to everyone
            let point_com = Point::from_scalar(curve, &poly_point);
            let mut point_com_raw = point_com.to_bytes();
            for ii in 0..playercount {
                if ii != playerindex {
                    send[ii].as_mut().unwrap().write(&point_com_raw)?;
                    send[ii].as_mut().unwrap().flush()?;
                }
            }

            // receive commitments to everyone's polynomial points
            for ii in 0..playercount {
                if ii == playerindex {
                    points_com.push(point_com.clone());
                } else {
                    recv[ii].as_mut().unwrap().read_exact(&mut point_com_raw)?;
                    points_com.push(Point::from_bytes(curve, &point_com_raw));
                }
            }
        }

        // for each contiguous set of parties, perform shamir reconsruction in the exponent and check the result against the known pk
        for ii in 0..(playercount - threshold + 1) {
            let mut recon_sum = Point::inf(curve);
            for jj in 0..threshold {
                let mut coefnum = Scalar::one(curve);
                let mut coefdenom = Scalar::one(curve);
                // calculate lagrange coefficient
                for kk in 0..threshold {
                    if kk != jj {
                        coefnum = coefnum.mul(&Scalar::from_u32(curve, (ii + kk + 1) as u32));
                        coefdenom = coefdenom.mul(
                            &Scalar::from_u32(curve, (ii + kk + 1) as u32)
                                .sub(&Scalar::from_u32(curve, (ii + jj + 1) as u32)),
                        );
                    }
                }
                let recon_frag = points_com[ii + jj].mul(&coefnum.mul(&coefdenom.inv()));
                recon_sum = recon_sum.add(&recon_frag);
            }
            recon_sum = recon_sum;
            if pk == Point::inf(curve) {
                pk = recon_sum;
            } else {
                assert_eq!(recon_sum, pk);
            }
        }

        // finally, each pair of parties must have multiplier setup between them. The player with the higher index is always Bob.
        let mut rngs = Vec::with_capacity(playercount);
        for _ in 0..playercount {
            rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
        }

        let threadcount = match std::env::var_os("RAYON_NUM_THREADS") {
            Some(val) => {
                let val = val.into_string().unwrap().parse().unwrap();
                if val > 0 {
                    val
                } else {
                    playercount
                }
            }
            None => playercount,
        };

        let rayonpool = rayon::ThreadPoolBuilder::new()
            .num_threads(threadcount)
            .build()
            .unwrap();
        let multipliervec = rayonpool.install(|| {
            send.par_iter_mut()
                .zip(recv.par_iter_mut())
                .zip(rngs.par_iter_mut())
                .enumerate()
                .map(|(ii, ((sendi, recvi), rngi))| {
                    if ii > playerindex {
                        MulPlayer::Sender(mul::MulSender::new(
                            curve,
                            &ro.get_dyadic_tagger(ii),
                            rngi,
                            recvi.as_mut().unwrap(),
                            sendi.as_mut().unwrap(),
                        ))
                    } else if ii < playerindex {
                        MulPlayer::Recver(
                            mul::MulRecver::new(
                                curve,
                                &ro.get_dyadic_tagger(ii),
								rngi,
                                recvi.as_mut().unwrap(),
                                sendi.as_mut().unwrap(),
                            )
                            .unwrap(),
                        )
                    } else {
                        MulPlayer::Null
                    }
                })
                .collect()
        });

        Ok(ThresholdSigner {
            ro: ro,
            playerindex: playerindex,
            threshold: threshold,
            multiplier: multipliervec,
            poly_point: poly_point,
            pk: pk,
            curve,
        })
    }

    pub fn sign<TR: Read + Send, TW: Write + Send, R: Rng>(
        &mut self,
        counterparties: &[usize],
        msg: &[u8],
        rng: &mut R,
        recv: &mut [Option<TR>],
        send: &mut [Option<TW>],
    ) -> Result<Option<(Scalar, Scalar)>, Box<dyn Error>> {
        assert_eq!(counterparties.len(), self.threshold - 1);

        if self.threshold == 2 {
            let counterparty = counterparties[0];
            if self.playerindex > counterparty {
                return Ok(Some(self.sign2t_bob(
                    counterparty,
                    msg,
                    rng,
                    &mut recv[counterparty].as_mut().unwrap(),
                    &mut send[counterparty].as_mut().unwrap(),
                )?));
            } else if self.playerindex < counterparty {
                self.sign2t_alice(
                    counterparty,
                    msg,
                    rng,
                    &mut recv[counterparty].as_mut().unwrap(),
                    &mut send[counterparty].as_mut().unwrap(),
                )?;
                return Ok(None);
            } else {
                panic!();
            }
        } else {
            let mut parties: Vec<usize> = counterparties.to_vec();
            parties.push(self.playerindex);
            parties.sort();
            return Ok(Some(self.sign_threshold(&parties, msg, rng, recv, send)?));
        }
    }

    pub fn sign_and_gen_refresh<TR: Read + Send, TW: Write + Send, R: Rng>(
        &mut self,
        counterparties: &[usize],
        msg: &[u8],
        tag: &[u8],
        rng: &mut R,
        recv: &mut [Option<TR>],
        send: &mut [Option<TW>],
    ) -> Result<(Option<(Scalar, Scalar)>, ProactiveRefreshPackage), Box<dyn Error>> {
        assert_eq!(counterparties.len(), self.threshold - 1);

        assert_eq!(self.threshold, 2);
        let counterparty = counterparties[0];

        if self.playerindex > counterparty {
            let (r, s, p) = self.sign2t_and_gen_refresh_bob(
                counterparty,
                msg,
                Some(tag),
                rng,
                recv[counterparty].as_mut().unwrap(),
                send[counterparty].as_mut().unwrap(),
            )?;
            return Ok((Some((r, s)), p.unwrap()));
        } else if self.playerindex < counterparty {
            return Ok((
                None,
                self.sign2t_and_gen_refresh_alice(
                    counterparty,
                    msg,
                    Some(tag),
                    rng,
                    recv[counterparty].as_mut().unwrap(),
                    send[counterparty].as_mut().unwrap(),
                )?
                .unwrap(),
            ));
        } else {
            panic!();
        }
    }

    pub fn apply_refresh(
        &mut self,
        refreshpackage: &ProactiveRefreshPackage,
    ) -> Result<(), Box<dyn Error>> {
        assert_eq!(self.threshold, 2);
        self.apply_refresh_2t(refreshpackage)
    }

    fn sign_threshold<TR: Read + Send, TW: Write + Send, R: Rng>(
        &mut self,
        counterparties: &[usize],
        msg: &[u8],
        rng: &mut R,
        recv: &mut [Option<TR>],
        send: &mut [Option<TW>],
    ) -> Result<(Scalar, Scalar), Box<dyn Error>> {
        let secp_bytes = self.curve.fq_bytes * 2 + 1;
        let fr_bytes = self.curve.fr_bytes;
        self.ro.apply_subgroup_list(counterparties)?;
        let sroindex = self.ro.current_broadcast_counter();

        let ki = self.curve.rand_scalar(rng);
        let kipad = self.curve.rand_scalar(rng);
        let kii = ki.inv();
        let kipadki = kii.mul(&kipad);

        // create reduced sets of resources for the multipliers
        let mut prunedrecv: Vec<&mut Option<TR>> = recv
            .iter_mut()
            .enumerate()
            .filter_map(|(index, val)| {
                if counterparties.contains(&index) {
                    Some(val)
                } else {
                    None
                }
            })
            .collect();
        let mut prunedsend: Vec<&mut Option<TW>> = send
            .iter_mut()
            .enumerate()
            .filter_map(|(index, val)| {
                if counterparties.contains(&index) {
                    Some(val)
                } else {
                    None
                }
            })
            .collect();
        let mut prunedmultiplier = self
            .multiplier
            .iter()
            .enumerate()
            .filter_map(|(index, val)| {
                if counterparties.contains(&index) {
                    Some(val)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let tempplayeri = self.playerindex;
        let prunedplayerindex = counterparties
            .iter()
            .position(|&x| x == tempplayeri)
            .unwrap();

        //instance key and inverse instance key multiplication

        let threadcount = match std::env::var_os("RAYON_NUM_THREADS") {
            Some(val) => {
                let val = val.into_string().unwrap().parse().unwrap();
                if val > 0 {
                    val
                } else {
                    counterparties.len()
                }
            }
            None => counterparties.len(),
        };

        let rayonpool = rayon::ThreadPoolBuilder::new()
            .num_threads(threadcount)
            .build()
            .unwrap();

        // message 1 send+recv, message 2 send
        let prodshares = mprmul_round_one(
            self.curve,
            4,
            prunedplayerindex,
            &mut prunedmultiplier,
            &self.ro,
            rng,
            &mut prunedrecv.as_mut_slice(),
            &mut prunedsend.as_mut_slice(),
            &rayonpool,
        );

        let mut helpfulsendbuffer = vec![Some(Cursor::new(Vec::new())); counterparties.len()];

        {
            let prodshares1: Vec<&[Scalar]> = prodshares
                .iter()
                .map(|x| if x.0.len() > 0 { &x.0[0..2] } else { &x.0[..] })
                .collect();

            // message 2 send
            mpmul_first(
                self.curve,
                &[ki.clone(), kipadki.clone()],
                prunedplayerindex,
                prodshares1.as_slice(),
                helpfulsendbuffer
                    .iter_mut()
                    .collect::<Vec<_>>()
                    .as_mut_slice(),
            )?;
        }

        let helpfulsentbuffer = helpfulsendbuffer
            .into_iter()
            .map(|x| x.unwrap().into_inner())
            .collect();

        // message 2 recv
        let linshares = mprmul_round_two(
            self.curve,
            prunedplayerindex,
            &prodshares,
            &mut prunedmultiplier,
            &self.ro,
            rng,
            &mut prunedrecv.as_mut_slice(),
            &mut prunedsend.as_mut_slice(),
            &rayonpool,
            Some(helpfulsentbuffer),
        );

        let shares: Vec<Vec<(Scalar, Scalar)>> = prodshares
            .into_iter()
            .zip(linshares.into_iter())
            .map(|(prodel, linel)| prodel.0.into_iter().zip(linel.into_iter()).collect())
            .collect();

        let shares1: Vec<&[(Scalar, Scalar)]> = shares
            .iter()
            .map(|x| if x.len() > 0 { &x[0..2] } else { &x[..] })
            .collect();

        let shares2: Vec<&[(Scalar, Scalar)]> = shares
            .iter()
            .map(|x| if x.len() > 0 { &x[2..4] } else { &x[..] })
            .collect();

        // message 2 recv, message 3 to log(n)+1 send+recv
        let mulresult = mpmul_rest(
            self.curve,
            &[ki, kipadki],
            prunedplayerindex,
            shares1.as_slice(),
            &mut prunedrecv.as_mut_slice(),
            &mut prunedsend.as_mut_slice(),
        )?;
        let ui = mulresult[0].clone();
        let vi = mulresult[1].clone();

        let mut coefnum = Scalar::one(self.curve);
        let mut coefdenom = Scalar::one(self.curve);
        // calculate lagrange coefficient
        for kk in 0..self.threshold {
            if kk != prunedplayerindex {
                coefnum = coefnum.mul(&Scalar::from_u32(
                    self.curve,
                    (counterparties[kk] + 1) as u32,
                ));
                coefdenom = coefdenom.mul(
                    &Scalar::from_u32(self.curve, (counterparties[kk] + 1) as u32)
                        .sub(&Scalar::from_u32(self.curve, (self.playerindex + 1) as u32)),
                );
            }
        }
        let zi = self.poly_point.mul(&coefnum.mul(&coefdenom.inv()));

        //secret key multiplication, step one
        // message log(n)+2 send
        mpswapmul_send(
            self.curve,
            &[(vi.clone(), zi.clone())],
            prunedplayerindex,
            shares2.as_slice(),
            &mut prunedsend.as_mut_slice(),
        );

        //R and phi commitment, plus broadcast RO sync
        let ri = Point::from_scalar(self.curve, &ui);
        let mut ri_raw = [self.ro.next_broadcast_tag(), ri.to_bytes()].concat();
        let mut pad_raw = [self.ro.next_broadcast_tag(), kipad.to_bytes()].concat();

        let mut doublecom = vec![[vec![0u8; HASH_SIZE], vec![0u8; HASH_SIZE]]; self.threshold];
        doublecom[prunedplayerindex] = [hash(&pad_raw), hash(&ri_raw)];

        // synchronize the random oracles
        let mut sroindex_raw = [0u8; 8];
        LittleEndian::write_u64(&mut sroindex_raw, sroindex);

        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+2 send
                prunedsend[ii].as_mut().unwrap().write(&sroindex_raw)?;
                prunedsend[ii]
                    .as_mut()
                    .unwrap()
                    .write(&doublecom[prunedplayerindex].concat())?;
                prunedsend[ii].as_mut().unwrap().flush()?;
            }
        }

        //secret key multiplication, step two
        // message log(n)+2 recv
        let wi = mpswapmul_recv(
            self.curve,
            &[(vi.clone(), zi)],
            prunedplayerindex,
            shares2.as_slice(),
            &mut prunedrecv.as_mut_slice(),
        )[0]
        .clone();

        // receive commitments to kjpad, rj, poks
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+2 recv
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut sroindex_raw)
                    .unwrap();
                self.ro.advance_counterparty_broadcast_counter(
                    counterparties[ii],
                    LittleEndian::read_u64(&sroindex_raw),
                );
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut doublecom[ii][0])?;
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut doublecom[ii][1])?;
            }
        }

        // release ri + pok
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+3 send
                prunedsend[ii]
                    .as_mut()
                    .unwrap()
                    .write(&ri_raw[RO_TAG_SIZE..])?;
                prunedsend[ii].as_mut().unwrap().flush()?;
            }
        }

        // receive rj + pok and verify against commitment
        let mut r = ri;
        let mut rjs = vec![Point::inf(self.curve); self.threshold];
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+3 recv
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut ri_raw[RO_TAG_SIZE..])?;
                ri_raw[0..RO_TAG_SIZE]
                    .copy_from_slice(&self.ro.next_counterparty_broadcast_tag(ii));
                assert_eq!(hash(&ri_raw), doublecom[ii][1]);
                rjs[ii] = Point::from_bytes(self.curve, &ri_raw[RO_TAG_SIZE..]);
                r = Point::add(&r, &rjs[ii]);
            }
        }

        // message log(n)+3 recv

        let mut checkpt1 = r.mul(&vi);
        let mut checkpt2 = Point::add(
            &self.pk.mul(&vi),
            &Point::from_scalar(self.curve, &wi).neg(),
        );
        let mut checkpt3 = r.mul(&wi);

        let mut checkpt123_raw = [
            self.ro.next_broadcast_tag(),
            checkpt1.to_bytes(),
            checkpt2.to_bytes(),
            checkpt3.to_bytes(),
        ]
        .concat();
        let mut checkpt123_coms = vec![vec![0u8; HASH_SIZE]; self.threshold];
        checkpt123_coms[prunedplayerindex] = hash(&checkpt123_raw);
        // send commitment
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+4 send
                prunedsend[ii]
                    .as_mut()
                    .unwrap()
                    .write(&checkpt123_coms[prunedplayerindex])?;
                prunedsend[ii].as_mut().unwrap().flush()?;
            }
        }

        // receive commitments checkpts
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+4 recv
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut checkpt123_coms[ii])?;
            }
        }

        // release kipad and checkpts
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+5 send
                prunedsend[ii]
                    .as_mut()
                    .unwrap()
                    .write(&pad_raw[(RO_TAG_SIZE)..])?;
                prunedsend[ii]
                    .as_mut()
                    .unwrap()
                    .write(&checkpt123_raw[(RO_TAG_SIZE)..])?;
                prunedsend[ii].as_mut().unwrap().flush()?;
            }
        }

        // receive kjpad and verify against commitment
        let mut kpad = kipad;
        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                pad_raw[0..RO_TAG_SIZE]
                    .copy_from_slice(&self.ro.next_counterparty_broadcast_tag(ii));
                // message log(n)+5 recv
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut pad_raw[RO_TAG_SIZE..])?;
                let comcomp = hash(&pad_raw);
                let kjpad = Scalar::from_bytes(self.curve, &pad_raw[RO_TAG_SIZE..]);
                assert_eq!(comcomp, doublecom[ii][0]);
                kpad = kpad.mul(&kjpad);

                checkpt123_raw[0..RO_TAG_SIZE]
                    .copy_from_slice(&self.ro.next_counterparty_broadcast_tag(ii));
                // message log(n)+5 recv
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut checkpt123_raw[RO_TAG_SIZE..])?;
                let mut comcomp = hash(&checkpt123_raw);
                assert_eq!(comcomp, checkpt123_coms[ii]);
                let checkpt1_frag = Point::from_bytes(
                    self.curve,
                    &checkpt123_raw[RO_TAG_SIZE..(secp_bytes + RO_TAG_SIZE)],
                );
                let checkpt2_frag = Point::from_bytes(
                    self.curve,
                    &checkpt123_raw[(secp_bytes + RO_TAG_SIZE)..(2 * secp_bytes + RO_TAG_SIZE)],
                );
                let checkpt3_frag = Point::from_bytes(
                    self.curve,
                    &checkpt123_raw[(2 * secp_bytes + RO_TAG_SIZE)..(3 * secp_bytes + RO_TAG_SIZE)],
                );
                checkpt1 = Point::add(&checkpt1, &checkpt1_frag);
                checkpt2 = Point::add(&checkpt2, &checkpt2_frag);
                checkpt3 = Point::add(&checkpt3, &checkpt3_frag);
            }
        }

        assert_ne!(kpad, Scalar::zero(self.curve));

        assert_eq!(checkpt1, Point::from_scalar(self.curve, &kpad));

        assert_eq!(checkpt2, Point::inf(self.curve));

        assert_eq!(checkpt3, self.pk.mul(&kpad));

        // hash the message
        let z = Scalar::from_bytes(self.curve, &hash(msg));

        let mut rxb = r.x_bytes();
        let rx = Scalar::from_bytes(self.curve, &rxb);

        let wiaug = wi.mul(&kpad.inv());
        let mut sig = z.mul(&vi).mul(&kpad.inv()).add(&wiaug.mul(&rx));
        let mut sig_frag_raw = sig.to_bytes();

        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+6 send
                prunedsend[ii].as_mut().unwrap().write(&sig_frag_raw)?;
                prunedsend[ii].as_mut().unwrap().flush()?;
            }
        }

        for ii in 0..self.threshold {
            if ii != prunedplayerindex {
                // message log(n)+6 recv
                prunedrecv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut sig_frag_raw)?;
                let sig_frag = Scalar::from_bytes(self.curve, &sig_frag_raw);
                sig = sig.add(&sig_frag);
            }
        }

        assert!(ecdsa_verify(
            self.curve,
            msg,
            (rx.clone(), sig.clone()),
            self.pk.clone()
        ));
        Ok((rx, sig))
    }

    fn sign2t_alice<TR: Read, TW: Write + Send, R: Rng>(
        &mut self,
        counterparty: usize,
        msg: &[u8],
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<(), Box<dyn Error>> {
        let res = self.sign2t_and_gen_refresh_alice(counterparty, msg, None, rng, recv, send);
        if res.is_ok() {
            Ok(())
        } else {
            Err(res.unwrap_err())
        }
    }

    fn sign2t_and_gen_refresh_alice<TR: Read, TW: Write + Send, R: Rng>(
        &mut self,
        counterparty: usize,
        msg: &[u8],
        tag: Option<&[u8]>,
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<Option<ProactiveRefreshPackage>, Box<dyn Error>> {
        let secp_bytes = self.curve.fq_bytes * 2 + 1;
        let fr_bytes = self.curve.fr_bytes;
        let (parties, prunedcpindex) = if self.playerindex > counterparty {
            ([counterparty, self.playerindex], 0)
        } else {
            ([self.playerindex, counterparty], 1)
        };
        self.ro.apply_subgroup_list(&parties)?;
        let sroindex = self.ro.current_broadcast_counter();
        let mut sroindex_raw = [0u8; 8];
        // precompute things you won't need till later

        // alice's instance key is of a special form for the two round version:
        // k_a = H(k'_a*G)+k'_a
        // this prevents her from choosing the value conveniently
        let kaprime = self.curve.rand_scalar(rng);
        let kapad = self.curve.rand_scalar(rng);

        // hash the message
        let z = Scalar::from_bytes(self.curve, &hash(msg));

        // calculate lagrange coefficient
        let mut coef = Scalar::from_u32(self.curve, (counterparty + 1) as u32);
        coef = coef.mul(
            &(Scalar::from_u32(self.curve, (counterparty + 1) as u32)
                .sub(&Scalar::from_u32(self.curve, (self.playerindex + 1) as u32)))
            .inv(),
        );
        let t0a = coef.mul(&self.poly_point);

        let multiplier = match self.multiplier[counterparty] {
            MulPlayer::Sender(ref multiplier) => multiplier,
            _ => {
                panic!()
            }
        };

        // online phase
        recv.read_exact(&mut sroindex_raw)?;
        self.ro.advance_counterparty_broadcast_counter(
            prunedcpindex,
            LittleEndian::read_u64(&sroindex_raw),
        );
        let dro = self.ro.get_dyadic_tagger(prunedcpindex);

        // recv D_b from bob
        let mut dbraw = vec![0u8; secp_bytes];
        recv.read_exact(&mut dbraw)?;
        let db = Point::from_bytes(self.curve, &dbraw);

        let rprime = db.mul(&kaprime);
        let rprimeraw = [dro.next_dyadic_tag(), rprime.to_bytes()].concat();
        let mut kaoffsetraw = hash(&rprimeraw);
        let kaoffset = Scalar::from_bytes(self.curve, &kaoffsetraw);
        let ka = kaoffset.add(&kaprime);

        let kai = ka.inv();
        let t0ai = kai.mul(&t0a);

        // compute R = k_a*k_b*G, and get the x coordinate
        let r = db.mul(&ka);
        let rxb = r.x_bytes();
        let rx = Scalar::from_bytes(self.curve, &rxb);
        let kapadda = Point::from_scalar(self.curve, &ka.mul(&kapad));

        // Prove knowledge of ka for R; hardcoded fiat-shamir so we can do preprocessing
        let kaproof_randcommitted = self.curve.rand_scalar(rng);

        let kaproof_randcommitment = db.mul(&kaproof_randcommitted);
        let kaproof_buf = [
            dro.next_dyadic_tag(),
            r.to_bytes(),
            kaproof_randcommitment.to_bytes(),
        ]
        .concat();
        let mut kaproof_challenge = hash(&kaproof_buf);
        let kaproof_challenge = Scalar::from_bytes(self.curve, &kaproof_challenge[..]);
        let kaproof_z = ka.mul(&kaproof_challenge).add(&kaproof_randcommitted);

        // generate OT extensions for two multiplications (input independent for alice)
        let extensions = multiplier.mul_extend(2, &dro, recv);

        // end first message (bob to alice)

        let mut bufsend = BufWriter::new(send);
        LittleEndian::write_u64(&mut sroindex_raw, sroindex);
        bufsend.write(&sroindex_raw)?;

        // alice sends D'_a = k'_a*G rather than D_a so that bob can check her work
        bufsend.write(&rprime.to_bytes())?;
        bufsend.write(&kaproof_randcommitment.to_bytes())?;
        bufsend.write(&kaproof_z.to_bytes())?;
        bufsend.flush()?;

        // optional: proactive refresh
        let (refreshpackage, mut bufsend) = if let Some(tag) = tag {
            let send = bufsend.into_inner().map_err(|_| "").unwrap();
            (
                Some(self.gen_refresh_2t(&r, tag, counterparty, prunedcpindex, rng, recv, send)?),
                BufWriter::new(send),
            )
        } else {
            (None, bufsend)
        };

        // perform two multiplications with 1/k_a and sk_a/k_a.
        let t12 = multiplier.mul_transfer(
            &[&kai.add(&kapad), &t0ai, &kai],
            &[
                extensions.0[0].clone(),
                extensions.0[0].clone(),
                extensions.0[1].clone(),
            ],
            &extensions.1,
            &dro,
            rng,
            &mut bufsend,
        )?;
        bufsend.flush()?;
        let t1a = t12[0].clone();
        let t2aa = t12[1].clone();
        let t2ba = t12[2].clone();
        let t2a = t2aa.add(&t2ba);

        // compute check value Gamma_1 for alice
        let gamma1 = Point::add(
            &Point::add(&r.mul(&t1a.neg()), &kapadda),
            &Point::gen(self.curve),
        );
        let gamma1raw = [dro.next_dyadic_tag(), gamma1.to_bytes()].concat();
        let mut enckey = hash(&gamma1raw);
        let mut kapadraw = kapad.to_bytes();
        for ii in 0..fr_bytes {
            kapadraw[ii] ^= enckey[ii];
        }
        bufsend.write(&kapadraw)?;
        bufsend.flush()?;

        // compute signature share m_a for alice
        let mut ma = t1a.mul(&z).add(&t2a.mul(&rx)).to_bytes();

        // compute check value Gamma_2, and encrypt m_a with H(Gamma_2)
        let t2ag = Point::from_scalar(self.curve, &t2a.neg());
        let t1apk = self.pk.mul(&t1a);
        let gamma2 = Point::add(&t2ag, &t1apk);
        let gamma2raw = [dro.next_dyadic_tag(), gamma2.to_bytes()].concat();
        let mut enckey = hash(&gamma2raw);
        for ii in 0..fr_bytes {
            ma[ii] ^= enckey[ii];
        }

        // send encrypted signature share
        bufsend.write(&ma)?;
        bufsend.flush()?;

        // end second message (alice to bob)

        Ok(refreshpackage)
    }

    fn sign2t_bob<TR: Read, TW: Write + Send, R: Rng>(
        &mut self,
        counterparty: usize,
        msg: &[u8],
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<(Scalar, Scalar), Box<dyn Error>> {
        let res = self.sign2t_and_gen_refresh_bob(counterparty, msg, None, rng, recv, send);
        if let Ok((r0, r1, _)) = res {
            Ok((r0, r1))
        } else {
            Err(res.unwrap_err())
        }
    }

    fn sign2t_and_gen_refresh_bob<TR: Read, TW: Write, R: Rng>(
        &mut self,
        counterparty: usize,
        msg: &[u8],
        tag: Option<&[u8]>,
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<(Scalar, Scalar, Option<ProactiveRefreshPackage>), Box<dyn Error>> {
        let secp_bytes = self.curve.fq_bytes * 2 + 1;
        let fr_bytes = self.curve.fr_bytes;
        let (parties, prunedcpindex) = if self.playerindex > counterparty {
            ([counterparty, self.playerindex], 0)
        } else {
            ([self.playerindex, counterparty], 1)
        };
        self.ro.apply_subgroup_list(&parties)?;
        let sroindex = self.ro.current_broadcast_counter();
        let mut sroindex_raw = [0u8; 8];
        LittleEndian::write_u64(&mut sroindex_raw, sroindex);

        let mut bufsend = BufWriter::new(send);
        bufsend.write(&sroindex_raw)?;

        let multiplier = match self.multiplier[counterparty] {
            MulPlayer::Recver(ref multiplier) => multiplier,
            _ => {
                panic!()
            }
        };
        // no precomputation - we want to begin writing as soon as possible

        // choose k_b, calc D_b = k_b*G, send D_b
        let kb = self.curve.rand_scalar(rng);
        let db = Point::from_scalar(self.curve, &kb);
        let mut dbraw = db.to_bytes();
        bufsend.write(&dbraw)?;
        bufsend.flush()?;

        // calculate lagrange coefficient
        let mut coef = Scalar::from_u32(self.curve, (counterparty + 1) as u32);
        coef = coef.mul(
            &(Scalar::from_u32(self.curve, (counterparty + 1) as u32)
                .sub(&Scalar::from_u32(self.curve, (self.playerindex + 1) as u32)))
            .inv(),
        );
        let t0b = coef.mul(&self.poly_point);

        let dro = self.ro.get_dyadic_tagger(prunedcpindex);
        let rprime_tag = dro.next_dyadic_tag();
        let kaproof_tag = dro.next_dyadic_tag();

        // generate OT extensions for multiplications with 1/k_b and sk_b/k_b
        let kbi = kb.inv();
        let t0bi = kbi.mul(&t0b);
        let betas = [kbi.clone(), t0bi.clone()];
        let extensions = multiplier.mul_encode_and_extend(&betas, &dro, rng, &mut bufsend)?;
        bufsend.flush()?;

        // end first message (bob to alice)
        recv.read_exact(&mut sroindex_raw)?;
        self.ro.advance_counterparty_broadcast_counter(
            prunedcpindex,
            LittleEndian::read_u64(&sroindex_raw),
        );

        // receive D'_a from alice, calculate D_a as D_a = H(D'_a)*G + D'_a
        let mut rprimeraw = vec![0u8; secp_bytes + RO_TAG_SIZE];
        recv.read_exact(&mut rprimeraw[RO_TAG_SIZE..])?;
        rprimeraw[0..RO_TAG_SIZE].copy_from_slice(&rprime_tag);
        let rprime = Point::from_bytes(self.curve, &rprimeraw[RO_TAG_SIZE..]);
        let mut kaoffsetraw = hash(&rprimeraw);
        let kaoffset = Scalar::from_bytes(self.curve, &kaoffsetraw);
        let kbkaoffsetg = Point::from_scalar(self.curve, &kb.mul(&kaoffset));

        // compute R = k_a*k_b*G, and get the x coordinate
        let r = Point::add(&kbkaoffsetg, &rprime);
        let mut rxb = r.x_bytes();
        let rx = Scalar::from_bytes(self.curve, &rxb);

        // verify alice's PoK of k_a for R
        let mut kaproof_buf = vec![0u8; 2 * secp_bytes + fr_bytes + RO_TAG_SIZE];
        kaproof_buf[0..RO_TAG_SIZE].copy_from_slice(&kaproof_tag);
        kaproof_buf[RO_TAG_SIZE..(secp_bytes + RO_TAG_SIZE)].copy_from_slice(&r.to_bytes());
        recv.read_exact(&mut kaproof_buf[(RO_TAG_SIZE + secp_bytes)..])?;
        let kaproof_randcommitment = Point::from_bytes(
            self.curve,
            &kaproof_buf[(RO_TAG_SIZE + secp_bytes)..(RO_TAG_SIZE + 2 * secp_bytes)],
        );
        let kaproof_z =
            Scalar::from_bytes(self.curve, &kaproof_buf[(RO_TAG_SIZE + 2 * secp_bytes)..]);
        let mut kaproof_challenge = hash(&kaproof_buf[0..(2 * secp_bytes + RO_TAG_SIZE)]);
        let kaproof_challenge = Scalar::from_bytes(self.curve, &kaproof_challenge[..]);
        let kaproof_lhs = Point::add(&r.mul(&kaproof_challenge), &kaproof_randcommitment);
        let kaproof_rhs = Point::from_scalar(self.curve, &kaproof_z.mul(&kb));
        assert_eq!(kaproof_lhs, kaproof_rhs);

        // optional: proactive refresh
        let refreshpackage = if let Some(tag) = tag {
            let send = bufsend.into_inner().map_err(|_| "").unwrap();
            Some(self.gen_refresh_2t(&r, tag, counterparty, prunedcpindex, rng, recv, send)?)
        } else {
            None
        };

        // hash message
        let z = hash(msg);
        let z = Scalar::from_bytes(self.curve, &z);

        // perform multiplications using the extensions we just generated
        let t12 = multiplier.mul_transfer(
            &[
                extensions.0[0].clone(),
                extensions.0[0].clone(),
                extensions.0[1].clone(),
            ],
            &extensions.1,
            &[
                extensions.2[0].clone(),
                extensions.2[0].clone(),
                extensions.2[1].clone(),
            ],
            &extensions.3,
            &dro,
            recv,
        )?;
        let t1b = t12[0].clone();
        let t2ab = t12[1].clone();
        let t2bb = t12[2].clone();
        let t2b = t2ab.add(&t2bb);
        let gamma1 = r.mul(&t1b); // start calculating gamma_b early, to give the sender extra time
        let gamma1raw = [dro.next_dyadic_tag(), gamma1.to_bytes()].concat();
        let mut enckey = hash(&gamma1raw);

        // compute the first check messages Gamma_1, and decrypt the pad
        let mut kapadraw = vec![0u8; fr_bytes];
        recv.read_exact(&mut kapadraw)?;
        for ii in 0..fr_bytes {
            kapadraw[ii] ^= enckey[ii];
        }
        let kapad = Scalar::from_bytes(self.curve, &kapadraw);

        let t1baug = t1b.sub(&kbi.mul(&kapad));
        let t2bg = Point::from_scalar(self.curve, &t2b);
        let t1bpk = self.pk.mul(&t1baug.neg());
        let gamma2 = Point::add(&t2bg, &t1bpk);
        let gamma2raw = [dro.next_dyadic_tag(), gamma2.to_bytes()].concat();
        let mut enckey = hash(&gamma2raw);

        // compute bob's signature share m_b
        let m_b = t1baug.mul(&z).add(&t2b.mul(&rx));

        // receive alice's signature share m_a, and decrypt using expected key
        let mut ma = vec![0u8; fr_bytes];
        recv.read_exact(&mut ma)?;
        for ii in 0..fr_bytes {
            ma[ii] ^= enckey[ii];
        }
        let m_a = Scalar::from_bytes(self.curve, &ma);

        // reconstruct signature
        let s = m_a.add(&m_b);

        // end second message (alice to bob)

        // verify signature. Abort if it's incorrect.
        assert!(ecdsa_verify(
            self.curve,
            msg,
            (rx.clone(), s.clone()),
            self.pk.clone()
        ));
        Ok((rx, s, refreshpackage))
    }

    fn gen_refresh_2t<TR: Read, TW: Write, R: Rng>(
        &self,
        R: &Point,
        tag: &[u8],
        counterparty: usize,
        prunedcpindex: usize,
        rng: &mut R,
        recv: &mut TR,
        send: &mut TW,
    ) -> Result<ProactiveRefreshPackage, Box<dyn Error>> {
        let my_coin = self.curve.rand_scalar(rng);
        let (my_nonce_dl, my_nonce) = self.curve.rand_scalar_and_point(rng);
        let mut coin_raw = [self.ro.next_broadcast_tag(), my_coin.to_bytes()].concat();
        let mut nonce_raw = my_nonce.to_bytes();
        let mut coincom = hash(&coin_raw);
        let (mut prfcom, proof) = prove_dl_fs_to_com(
            self.curve,
            &my_nonce_dl,
            &my_nonce,
            &ModelessGroupROTagger::new(&self.ro, false),
			rng
        )
        .unwrap();
        send.write(&coincom)?;
        send.write(&prfcom)?;
        send.flush()?;

        recv.read_exact(&mut coincom)?;
        recv.read_exact(&mut prfcom)?;

        send.write(&coin_raw[RO_TAG_SIZE..])?;
        send.write(&nonce_raw)?;
        send.write(&proof)?;
        send.flush()?;

        recv.read_exact(&mut coin_raw[RO_TAG_SIZE..])?;
        coin_raw[0..RO_TAG_SIZE]
            .copy_from_slice(&self.ro.next_counterparty_broadcast_tag(prunedcpindex)[..]);
        let mut coincomcomp = hash(&coin_raw);
        assert_eq!(coincom, coincomcomp);

        recv.read_exact(&mut nonce_raw)?;
        let cp_nonce = Point::from_bytes(self.curve, &nonce_raw);
        let proofresult = verify_dl_fs_with_com(
            self.curve,
            &cp_nonce,
            &prfcom,
            &ModelessDyadicROTagger::new(&self.ro.get_dyadic_tagger(prunedcpindex), false),
            recv,
        )?;

        assert!(proofresult);

        let schnorr_nonce = Point::add(&my_nonce, &cp_nonce);
        let coin = my_coin.add(&Scalar::from_bytes(self.curve, &coin_raw[RO_TAG_SIZE..]));

        let schnorr_e_in = [
            R.to_bytes(),
            schnorr_nonce.to_bytes(),
            coin.to_bytes(),
            vec![0u8; tag.len()],
        ]
        .concat();

        let mut schnorr_e = hash(&schnorr_e_in);
        let schnorr_e = Scalar::from_bytes(self.curve, &schnorr_e);

        // calculate lagrange coefficient
        let mut coef = Scalar::from_u32(self.curve, (counterparty + 1) as u32);
        coef = coef.mul(
            &(Scalar::from_u32(self.curve, (counterparty + 1) as u32)
                .sub(&Scalar::from_u32(self.curve, (self.playerindex + 1) as u32)))
            .inv(),
        );
        let my_sk = coef.mul(&self.poly_point);
        let schnorr_z = my_sk.mul(&schnorr_e).add(&my_nonce_dl);
        let mut schnorr_z_raw = schnorr_z.to_bytes();

        send.write(&schnorr_z_raw)?;
        send.flush()?;
        recv.read_exact(&mut schnorr_z_raw)?;
        let cp_schnorr_z = Scalar::from_bytes(self.curve, &schnorr_z_raw);

        let cp_pk_e =
            Point::add(&self.pk, &Point::from_scalar(self.curve, &my_sk).neg()).mul(&schnorr_e);

        assert_eq!(
            Point::from_scalar(self.curve, &cp_schnorr_z),
            Point::add(&cp_pk_e, &cp_nonce)
        );

        Ok((
            R.clone(),
            tag.to_vec(),
            coin,
            schnorr_nonce,
            schnorr_z.add(&cp_schnorr_z),
        ))
    }

    fn apply_refresh_2t(
        &mut self,
        refreshpackage: &ProactiveRefreshPackage,
    ) -> Result<(), Box<dyn Error>> {
        let (R, tag, coin, schnorr_nonce, schnorr_z) = refreshpackage;
        self.ro.remove_subgroup_mask();

        let schnorr_e_in = [
            R.to_bytes(),
            schnorr_nonce.to_bytes(),
            coin.to_bytes(),
            vec![0u8; tag.len()],
        ]
        .concat();

        let mut schnorr_e = hash(&schnorr_e_in);
        let schnorr_e = Scalar::from_bytes(self.curve, &schnorr_e);

        assert_eq!(
            Point::from_scalar(self.curve, &schnorr_z),
            Point::add(&self.pk.mul(&schnorr_e), &schnorr_nonce)
        );

        self.poly_point = self
            .poly_point
            .add(&coin.mul(&Scalar::from_u32(self.curve, (self.playerindex + 1) as u32)));
        for (ii, mulinstance) in self.multiplier.iter_mut().enumerate() {
            match mulinstance {
                MulPlayer::Sender(m) => {
                    m.apply_refresh(&coin.to_bytes(), &self.ro.get_dyadic_tagger(ii))
                        .unwrap();
                }
                MulPlayer::Recver(m) => {
                    m.apply_refresh(&coin.to_bytes(), &self.ro.get_dyadic_tagger(ii))
                        .unwrap();
                }
                MulPlayer::Null => {}
            };
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::P521;

    use super::channelstream::*;
    use super::*;
    use rand::RngCore;
    use std::thread;
    use test::Bencher;

    #[test]
    fn test_mpecdsa_2psign() {
        let curve = &P521;
        let msg = "The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes();
        let mut rng = rand::thread_rng();
        let ska = curve.rand_scalar(&mut rng);
        let skb = curve.rand_scalar(&mut rng);

        let (mut writ_a, mut read_b) = channelstream::new_channelstream();
        let (mut writ_b, mut read_a) = channelstream::new_channelstream();

        let thandle = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let bob = Bob2P::new(curve, &skb, &mut rng, &mut read_b, &mut writ_b).unwrap();

            let mut results = Vec::with_capacity(10);
            for _ in 0..10 {
                results.push(bob.sign(&msg, &mut rng, &mut read_b, &mut writ_b).unwrap());
            }

            results
        });

        let alice = Alice2P::new(curve, &ska, &mut rng, &mut read_a, &mut writ_a);
        assert!(alice.is_ok());
        let alice = alice.unwrap();
        for _ in 0..10 {
            alice
                .sign(&msg, &mut rng, &mut read_a, &mut writ_a)
                .unwrap();
        }
        thandle.join().unwrap();
    }

    #[test]
    fn test_mpecdsa_3p2tsetup() {
        let curve = &P521;
        let threshold = 2;
        let parties = 3;

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                thread::spawn(move || {
                    let mut rng = rand::thread_rng();
                    let mut sin = si;
                    let mut rin = ri;
                    ThresholdSigner::new(curve, ii, threshold, &mut rng, &mut rin, &mut sin)
                        .unwrap()
                })
            })
            .collect::<Vec<_>>();

        let mut firstpk = Point::inf(curve);
        for handle in thandles {
            let signer = handle.join().unwrap();
            if firstpk == Point::inf(curve) {
                firstpk = signer.pk;
            } else {
                assert_eq!(signer.pk, firstpk);
            }
        }
    }

    #[test]
    fn test_mpecdsa_3p2tsign() {
        let curve = &P521;
        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(3);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandlea = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut alice =
                ThresholdSigner::new(curve, 0, 2, &mut rng, &mut r0[..], &mut s0[..]).unwrap();
            let result1 = alice
                .sign(
                    &[1],
                    &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            let result2 = alice
                .sign(
                    &[2],
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            (result1, result2)
        });

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let thandleb = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut bob =
                ThresholdSigner::new(curve, 1, 2, &mut rng, &mut r1[..], &mut s1[..]).unwrap();
            let result1 = bob
                .sign(
                    &[0],
                    &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            let result2 = bob
                .sign(
                    &[2],
                    &"Lorem ipsum dolor sit amet".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            (result1, result2)
        });

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let thandlec = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut charlie =
                ThresholdSigner::new(curve, 2, 2, &mut rng, &mut r2[..], &mut s2[..]).unwrap();
            let result1 = charlie
                .sign(
                    &[0],
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            let result2 = charlie
                .sign(
                    &[1],
                    &"Lorem ipsum dolor sit amet".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            (result1, result2)
        });

        let alice = thandlea.join().unwrap();
        let bob = thandleb.join().unwrap();
        let charlie = thandlec.join().unwrap();
    }

    #[test]
    fn test_mpecdsa_3p2trefresh_gen() {
        let curve = &P521;

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(3);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandlea = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut alice =
                ThresholdSigner::new(curve, 0, 2, &mut rng, &mut r0[..], &mut s0[..]).unwrap();
            let result1 = alice
                .sign_and_gen_refresh(
                    &[1],
                    &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                    &"YW".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            let result2 = alice
                .sign_and_gen_refresh(
                    &[2],
                    &"etaoin shrdlu".as_bytes(),
                    &"YTMP".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            (result1, result2)
        });

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let thandleb = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut bob =
                ThresholdSigner::new(curve, 1, 2, &mut rng, &mut r1[..], &mut s1[..]).unwrap();
            let result1 = bob
                .sign_and_gen_refresh(
                    &[0],
                    &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                    &"YW".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            let result2 = bob
                .sign_and_gen_refresh(
                    &[2],
                    &"Lorem ipsum dolor sit amet".as_bytes(),
                    &"YWQMD".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            (result1, result2)
        });

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let thandlec = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut charlie =
                ThresholdSigner::new(curve, 2, 2, &mut rng, &mut r2[..], &mut s2[..]).unwrap();
            let result1 = charlie
                .sign_and_gen_refresh(
                    &[0],
                    &"etaoin shrdlu".as_bytes(),
                    &"YTMP".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            let result2 = charlie
                .sign_and_gen_refresh(
                    &[1],
                    &"Lorem ipsum dolor sit amet".as_bytes(),
                    &"YWQMD".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            (result1, result2)
        });

        let alice = thandlea.join().unwrap();
        let bob = thandleb.join().unwrap();
        let charlie = thandlec.join().unwrap();
    }

    #[test]
    fn test_mpecdsa_3p2trefresh_gen_apply() {
        let curve = &P521;

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(3);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandlea = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut alice =
                ThresholdSigner::new(curve, 0, 2, &mut rng, &mut r0[..], &mut s0[..]).unwrap();
            let result1 = alice
                .sign_and_gen_refresh(
                    &[1],
                    &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                    &"YW".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            let result2 = alice
                .sign_and_gen_refresh(
                    &[2],
                    &"etaoin shrdlu".as_bytes(),
                    &"YTMP".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            (result1, result2, alice)
        });

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let thandleb = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut bob =
                ThresholdSigner::new(curve, 1, 2, &mut rng, &mut r1[..], &mut s1[..]).unwrap();
            let result1 = bob
                .sign_and_gen_refresh(
                    &[0],
                    &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                    &"YW".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            let result2 = bob
                .sign_and_gen_refresh(
                    &[2],
                    &"Lorem ipsum dolor sit amet".as_bytes(),
                    &"YWQMD".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            (result1, result2, bob)
        });

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let thandlec = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut charlie =
                ThresholdSigner::new(curve, 2, 2, &mut rng, &mut r2[..], &mut s2[..]).unwrap();
            let result1 = charlie
                .sign_and_gen_refresh(
                    &[0],
                    &"etaoin shrdlu".as_bytes(),
                    &"YTMP".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            let result2 = charlie
                .sign_and_gen_refresh(
                    &[1],
                    &"Lorem ipsum dolor sit amet".as_bytes(),
                    &"YWQMD".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            (result1, result2, charlie)
        });

        let aliceout = thandlea.join().unwrap();
        let bobout = thandleb.join().unwrap();
        let charlieout = thandlec.join().unwrap();

        if let (
            ((_, ar0), (_, ar1), mut alice),
            ((_, br0), (_, br1), mut bob),
            ((_, cr0), (_, cr1), mut charlie),
        ) = (aliceout, bobout, charlieout)
        {
            for refpack in [ar0, br0, cr0, ar1, br1, cr1].iter() {
                assert!(alice.apply_refresh(&refpack).is_ok());
                assert!(bob.apply_refresh(&refpack).is_ok());
                assert!(charlie.apply_refresh(&refpack).is_ok());
            }

            let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(3);

            let mut s0 = sendvec.remove(0);
            let mut r0 = recvvec.remove(0);

            let thandlea = thread::spawn(move || {
                let mut rng = rand::thread_rng();
                let result1 = alice
                    .sign_and_gen_refresh(
                        &[1],
                        &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                        &"YW".as_bytes(),
                        &mut rng,
                        &mut r0[..],
                        &mut s0[..],
                    )
                    .unwrap();
                let result2 = alice
                    .sign_and_gen_refresh(
                        &[2],
                        &"etaoin shrdlu".as_bytes(),
                        &"YTMP".as_bytes(),
                        &mut rng,
                        &mut r0[..],
                        &mut s0[..],
                    )
                    .unwrap();
                (result1, result2)
            });

            let mut s1 = sendvec.remove(0);
            let mut r1 = recvvec.remove(0);

            let thandleb = thread::spawn(move || {
                let mut rng = rand::thread_rng();
                let result1 = bob
                    .sign_and_gen_refresh(
                        &[0],
                        &"The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes(),
                        &"YW".as_bytes(),
                        &mut rng,
                        &mut r1[..],
                        &mut s1[..],
                    )
                    .unwrap();
                let result2 = bob
                    .sign_and_gen_refresh(
                        &[2],
                        &"Lorem ipsum dolor sit amet".as_bytes(),
                        &"YWQMD".as_bytes(),
                        &mut rng,
                        &mut r1[..],
                        &mut s1[..],
                    )
                    .unwrap();
                (result1, result2)
            });

            let mut s2 = sendvec.remove(0);
            let mut r2 = recvvec.remove(0);

            let thandlec = thread::spawn(move || {
                let mut rng = rand::thread_rng();
                let result1 = charlie
                    .sign_and_gen_refresh(
                        &[0],
                        &"etaoin shrdlu".as_bytes(),
                        &"YTMP".as_bytes(),
                        &mut rng,
                        &mut r2[..],
                        &mut s2[..],
                    )
                    .unwrap();
                let result2 = charlie
                    .sign_and_gen_refresh(
                        &[1],
                        &"Lorem ipsum dolor sit amet".as_bytes(),
                        &"YWQMD".as_bytes(),
                        &mut rng,
                        &mut r2[..],
                        &mut s2[..],
                    )
                    .unwrap();
                (result1, result2)
            });

            let aliceout = thandlea.join().unwrap();

            let bobout = thandleb.join().unwrap();

            let charlieout = thandlec.join().unwrap();
        } else {
            assert!(false);
        }
    }

    #[test]
    fn test_mpecdsa_3p3tsign() {
        let curve = &P521;

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(3);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandlea = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut alice =
                ThresholdSigner::new(curve, 0, 3, &mut rng, &mut r0[..], &mut s0[..]).unwrap();
            let result1 = alice
                .sign(
                    &[1, 2],
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
            result1
        });

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let thandleb = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut bob =
                ThresholdSigner::new(curve, 1, 3, &mut rng, &mut r1[..], &mut s1[..]).unwrap();
            let result1 = bob
                .sign(
                    &[0, 2],
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r1[..],
                    &mut s1[..],
                )
                .unwrap();
            result1
        });

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let thandlec = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut charlie =
                ThresholdSigner::new(curve, 2, 3, &mut rng, &mut r2[..], &mut s2[..]).unwrap();
            let result1 = charlie
                .sign(
                    &[0, 1],
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
            result1
        });

        let alice = thandlea.join().unwrap();
        let bob = thandleb.join().unwrap();
        let charlie = thandlec.join().unwrap();
    }

    #[test]
    fn test_mpecdsa_7p4tsetup() {
        let curve = &P521;

        let threshold = 4;
        let parties = 7;

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                thread::spawn(move || {
                    let mut rng = rand::thread_rng();
                    let mut sin = si;
                    let mut rin = ri;
                    ThresholdSigner::new(curve, ii, threshold, &mut rng, &mut rin, &mut sin)
                        .unwrap()
                })
            })
            .collect::<Vec<_>>();

        let mut firstpk = Point::inf(curve);
        for handle in thandles {
            let signer = handle.join().unwrap();
            if firstpk == Point::inf(curve) {
                firstpk = signer.pk;
            } else {
                assert_eq!(signer.pk, firstpk);
            }
        }
    }

    #[test]
    fn test_mpecdsa_7p3tsetup() {
        let curve = &P521;

        let threshold = 3;
        let parties = 7;

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                thread::spawn(move || {
                    let mut rng = rand::thread_rng();
                    let mut sin = si;
                    let mut rin = ri;
                    ThresholdSigner::new(curve, ii, threshold, &mut rng, &mut rin, &mut sin)
                        .unwrap()
                })
            })
            .collect::<Vec<_>>();

        let mut firstpk = Point::inf(curve);
        for handle in thandles {
            let signer = handle.join().unwrap();
            if firstpk == Point::inf(curve) {
                firstpk = signer.pk;
            } else {
                assert_eq!(signer.pk, firstpk);
            }
        }
    }

    #[test]
    fn test_mpecdsa_7p5tsign() {
        let curve = &P521;

        let threshold = 5;
        let parties: usize = 7;

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);
        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                thread::spawn(move || {
                    let mut rng = rand::thread_rng();
                    let mut sin = si;
                    let mut rin = ri;
                    let mut signer = ThresholdSigner::new(
                        curve,
                        ii,
                        threshold,
                        &mut rng,
                        &mut rin[..],
                        &mut sin[..],
                    )
                    .unwrap();
                    if ii < threshold {
                        signer
                            .sign(
                                &(0usize..ii)
                                    .chain((ii + 1)..threshold)
                                    .collect::<Vec<usize>>(),
                                &"etaoin shrdlu".as_bytes(),
                                &mut rng,
                                &mut rin[..],
                                &mut sin[..],
                            )
                            .unwrap()
                    } else {
                        None
                    }
                })
            })
            .collect::<Vec<_>>();

        let mut somecount = 0;
        for handle in thandles {
            let result = handle.join().unwrap();

            if result.is_some() {
                somecount += 1;
            }
        }
        assert_eq!(somecount, threshold);
    }

    #[bench]
    fn bench_ecdsa_2psign(b: &mut Bencher) -> () {
        let curve = &P521;

        let msg = "The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes();
        let mut rng = rand::thread_rng();
        let ska = curve.rand_scalar(&mut rng);
        let skb = curve.rand_scalar(&mut rng);

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(2);

        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);

        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let thandle = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let bob = Bob2P::new(
                curve,
                &skb,
                &mut rng,
                &mut r1[1].as_mut().unwrap(),
                &mut s1[1].as_mut().unwrap(),
            )
            .expect("Failed to instantiate Bob");

            let mut keepgoing = [1u8; 1];

            r1[1]
                .as_mut()
                .unwrap()
                .read_exact(&mut keepgoing)
                .expect("Bob failed to read (1)");
            while keepgoing[0] > 0 {
                bob.sign(
                    &msg,
                    &mut rng,
                    &mut r1[1].as_mut().unwrap(),
                    &mut s1[1].as_mut().unwrap(),
                )
                .expect("Bob failed to sign");
                r1[1]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut keepgoing)
                    .expect("Bob failed to read (2)");
            }
        });

        let alice = Alice2P::new(
            curve,
            &ska,
            &mut rng,
            &mut r2[0].as_mut().unwrap(),
            &mut s2[0].as_mut().unwrap(),
        )
        .expect("Failed to instantiate Alice");
        b.iter(|| {
            s2[0]
                .as_mut()
                .unwrap()
                .write(&[1])
                .expect("Alice failed to write (1)");
            s2[0]
                .as_mut()
                .unwrap()
                .flush()
                .expect("Alice failed to flush");
            alice
                .sign(
                    &msg,
                    &mut rng,
                    &mut r2[0].as_mut().unwrap(),
                    &mut s2[0].as_mut().unwrap(),
                )
                .expect("Bob failed to sign");
        });
        s2[0]
            .as_mut()
            .unwrap()
            .write(&[0])
            .expect("Alice failed to write (2)");
        s2[0]
            .as_mut()
            .unwrap()
            .flush()
            .expect("Alice failed to flush");

        thandle.join().unwrap();
    }

    #[bench]
    fn bench_ecdsa_3p2tsetup(b: &mut Bencher) -> () {
        let curve = &P521;

        let mut rng = rand::thread_rng();
        let threshold = 2;
        let parties = 3;

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(parties);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(iiminusone, (si, ri))| {
                thread::spawn(move || {
                    let ii = iiminusone + 1;
                    let mut sin = si;
                    let mut rin = ri;
                    let mut rng = rand::thread_rng();

                    let mut keepgoing = [1u8; 1];
                    rin[0]
                        .as_mut()
                        .unwrap()
                        .read_exact(&mut keepgoing)
                        .expect(&format!("Party {} failed to read (1)", ii));
                    while keepgoing[0] > 0 {
                        ThresholdSigner::new(
                            curve,
                            ii,
                            threshold,
                            &mut rng,
                            &mut rin[..],
                            &mut sin[..],
                        )
                        .expect(&format!("Party {} failed to setup", ii));
                        rin[0]
                            .as_mut()
                            .unwrap()
                            .read_exact(&mut keepgoing)
                            .expect(&format!("Party {} failed to read (2)", ii));
                    }
                })
            })
            .collect::<Vec<_>>();

        b.iter(|| {
            for ii in 1..parties {
                s0[ii]
                    .as_mut()
                    .unwrap()
                    .write(&[1])
                    .expect("Party 0 failed to write (1)");
                s0[ii]
                    .as_mut()
                    .unwrap()
                    .flush()
                    .expect("Party 0 failed to flush");
            }
            ThresholdSigner::new(curve, 0, threshold, &mut rng, &mut r0[..], &mut s0[..])
                .expect("Party 0 failed to setup");
        });
        for ii in 1..parties {
            s0[ii]
                .as_mut()
                .unwrap()
                .write(&[0])
                .expect("Party 0 failed to write (2)");
            s0[ii]
                .as_mut()
                .unwrap()
                .flush()
                .expect("Party 0 failed to flush");
        }
        for handle in thandles {
            handle.join().unwrap();
        }
    }

    #[bench]
    fn bench_ecdsa_3p2tsign(b: &mut Bencher) -> () {
        let curve = &P521;

        let msg = "The Quick Brown Fox Jumped Over The Lazy Dog".as_bytes();

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(3);
        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);
        let mut s1 = sendvec.remove(0);
        let mut r1 = recvvec.remove(0);
        let mut s2 = sendvec.remove(0);
        let mut r2 = recvvec.remove(0);

        let thandlec = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut charlie =
                ThresholdSigner::new(curve, 2, 2, &mut rng, &mut r2[..], &mut s2[..]).unwrap();
            charlie
                .sign(
                    &[0],
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r2[..],
                    &mut s2[..],
                )
                .unwrap();
        });

        let thandleb = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut bob =
                ThresholdSigner::new(curve, 1, 2, &mut rng, &mut r1[..], &mut s1[..]).unwrap();
            let mut keepgoing = [1u8; 1];
            r1[0]
                .as_mut()
                .unwrap()
                .read_exact(&mut keepgoing)
                .expect("Bob failed to read (1)");
            while keepgoing[0] > 0 {
                bob.sign(&[0], &msg, &mut rng, &mut r1[..], &mut s1[..])
                    .expect("Bob failed to sign");
                r1[0]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut keepgoing)
                    .expect("Bob failed to read (2)");
            }
        });

        let mut rng = rand::thread_rng();

        let mut alice =
            ThresholdSigner::new(curve, 0, 2, &mut rng, &mut r0[..], &mut s0[..]).unwrap();
        alice
            .sign(
                &[2],
                &"etaoin shrdlu".as_bytes(),
                &mut rng,
                &mut r0[..],
                &mut s0[..],
            )
            .unwrap();
        thandlec.join().unwrap();

        b.iter(|| {
            s0[1]
                .as_mut()
                .unwrap()
                .write(&[1])
                .expect("Alice failed to write (1)");
            s0[1]
                .as_mut()
                .unwrap()
                .flush()
                .expect("Alice failed to flush");
            alice
                .sign(&[1], &msg, &mut rng, &mut r0[..], &mut s0[..])
                .expect("Alice failed to sign");
        });
        s0[1]
            .as_mut()
            .unwrap()
            .write(&[0])
            .expect("Alice failed to write (2)");
        s0[1]
            .as_mut()
            .unwrap()
            .flush()
            .expect("Alice failed to flush");
        thandleb.join().unwrap();
    }

    #[bench]
    fn bench_ecdsa_3p3tsign(b: &mut Bencher) {
        let curve = &P521;

        let parties = 3;
        let threshold = 3;

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(parties);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(iiminusone, (si, ri))| {
                thread::spawn(move || {
                    let ii = iiminusone + 1;
                    let mut sin = si;
                    let mut rin = ri;
                    let mut rng = rand::thread_rng();
                    let mut rngs = Vec::with_capacity(parties);
                    for _ in 0..parties {
                        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
                    }

                    let mut signer = ThresholdSigner::new(
                        curve,
                        ii,
                        threshold,
                        &mut rng,
                        &mut rin[..],
                        &mut sin[..],
                    )
                    .unwrap();

                    let mut keepgoing = [1u8; 1];
                    rin[0]
                        .as_mut()
                        .unwrap()
                        .read_exact(&mut keepgoing)
                        .expect(&format!("Party {} failed to read (1)", ii));
                    while keepgoing[0] > 0 {
                        if ii < threshold {
                            signer
                                .sign(
                                    &(0usize..ii)
                                        .chain((ii + 1)..threshold)
                                        .collect::<Vec<usize>>(),
                                    &"etaoin shrdlu".as_bytes(),
                                    &mut rng,
                                    &mut rin[..],
                                    &mut sin[..],
                                )
                                .unwrap();
                        }
                        rin[0]
                            .as_mut()
                            .unwrap()
                            .read_exact(&mut keepgoing)
                            .expect(&format!("Party {} failed to read (2)", ii));
                    }
                })
            })
            .collect::<Vec<_>>();

        let mut rng = rand::thread_rng();
        let mut rngs = Vec::with_capacity(parties);
        for _ in 0..parties {
            rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
        }

        let mut signer =
            ThresholdSigner::new(curve, 0, threshold, &mut rng, &mut r0[..], &mut s0[..]).unwrap();

        b.iter(|| {
            for ii in 1..parties {
                s0[ii]
                    .as_mut()
                    .unwrap()
                    .write(&[1])
                    .expect("Party 0 failed to write (1)");
                s0[ii]
                    .as_mut()
                    .unwrap()
                    .flush()
                    .expect("Party 0 failed to flush");
            }
            signer
                .sign(
                    &(1..(threshold)).collect::<Vec<usize>>(),
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
        });

        for ii in 1..parties {
            s0[ii]
                .as_mut()
                .unwrap()
                .write(&[0])
                .expect("Party 0 failed to write (2)");
            s0[ii]
                .as_mut()
                .unwrap()
                .flush()
                .expect("Party 0 failed to flush");
        }
        for handle in thandles {
            handle.join().unwrap();
        }
    }

    #[bench]
    fn bench_ecdsa_7p7tsign(b: &mut Bencher) {
        let curve = &P521;

        let parties = 7;
        let threshold = 7;

        let (mut sendvec, mut recvvec) = spawn_n2_channelstreams(parties);

        let mut s0 = sendvec.remove(0);
        let mut r0 = recvvec.remove(0);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(iiminusone, (si, ri))| {
                thread::spawn(move || {
                    let ii = iiminusone + 1;
                    let mut sin = si;
                    let mut rin = ri;
                    let mut rng = rand::thread_rng();
                    let mut rngs = Vec::with_capacity(parties);
                    for _ in 0..parties {
                        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
                    }

                    let mut signer = ThresholdSigner::new(
                        curve,
                        ii,
                        threshold,
                        &mut rng,
                        &mut rin[..],
                        &mut sin[..],
                    )
                    .unwrap();

                    let mut keepgoing = [1u8; 1];
                    rin[0]
                        .as_mut()
                        .unwrap()
                        .read_exact(&mut keepgoing)
                        .expect(&format!("Party {} failed to read (1)", ii));
                    while keepgoing[0] > 0 {
                        if ii < threshold {
                            signer
                                .sign(
                                    &(0usize..ii)
                                        .chain((ii + 1)..threshold)
                                        .collect::<Vec<usize>>(),
                                    &"etaoin shrdlu".as_bytes(),
                                    &mut rng,
                                    &mut rin[..],
                                    &mut sin[..],
                                )
                                .unwrap();
                        }
                        rin[0]
                            .as_mut()
                            .unwrap()
                            .read_exact(&mut keepgoing)
                            .expect(&format!("Party {} failed to read (2)", ii));
                    }
                })
            })
            .collect::<Vec<_>>();

        let mut rng = rand::thread_rng();
        let mut rngs = Vec::with_capacity(parties);
        for _ in 0..parties {
            rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
        }

        let mut signer =
            ThresholdSigner::new(curve, 0, threshold, &mut rng, &mut r0[..], &mut s0[..]).unwrap();

        b.iter(|| {
            for ii in 1..parties {
                s0[ii]
                    .as_mut()
                    .unwrap()
                    .write(&[1])
                    .expect("Party 0 failed to write (1)");
                s0[ii]
                    .as_mut()
                    .unwrap()
                    .flush()
                    .expect("Party 0 failed to flush");
            }
            signer
                .sign(
                    &(1..(threshold)).collect::<Vec<usize>>(),
                    &"etaoin shrdlu".as_bytes(),
                    &mut rng,
                    &mut r0[..],
                    &mut s0[..],
                )
                .unwrap();
        });

        for ii in 1..parties {
            s0[ii]
                .as_mut()
                .unwrap()
                .write(&[0])
                .expect("Party 0 failed to write (2)");
            s0[ii]
                .as_mut()
                .unwrap()
                .flush()
                .expect("Party 0 failed to flush");
        }
        for handle in thandles {
            handle.join().unwrap();
        }
    }
}
