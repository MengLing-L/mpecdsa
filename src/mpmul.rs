/***********
 * This module implements the multi-party multiplication protocol
 * described in the paper "Threshold ECDSA from ECDSA Assumptions"
 * by Doerner, Kondi, Lee, and shelat
 *
 * It relies upon the two-party random multiplication protocol in mul.rs
 ***********/

use std::cmp::min;
use std::mem::size_of_val;
use std::result::Result;

use rand::rngs::ThreadRng;
use rand::{Rng, SeedableRng};

use rand_chacha::ChaChaRng;
use rayon::prelude::*;
use rayon::ThreadPool;

use crate::utils::{Curve, Scalar};

use super::mul::*;
use super::ro::*;
use super::*;
use std::error::Error;

pub fn mpmul_round<TR: Read + std::marker::Send, TW: Write + std::marker::Send>(
    curve: &'static Curve,
    round: usize,
    inputs: &[Scalar],
    playerindex: usize,
    shares: &[&[(Scalar, Scalar)]],
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
) -> Vec<Scalar> {
    let fr_bytes = curve.fr_bytes;
    assert_eq!(recv.len(), send.len());
    let playercount = recv.len();

    let mut betas = inputs.to_vec();

    let thislevel = (playerindex >> round) << round;
    let discriminator = thislevel + (1 << (round - 1));
    let thislevelbase = if playerindex < discriminator {
        min(discriminator, playercount)
    } else {
        thislevel
    };
    let thislevelparties = min(playercount - thislevelbase, 1 << (round - 1));

    send[thislevelbase..(thislevelbase + thislevelparties)]
        .iter_mut()
        .zip(shares[thislevelbase..(thislevelbase + thislevelparties)].iter())
        .enumerate()
        .map(|(jj, (sendi, shares))| {
            let counterparty = thislevelbase + jj;

            if counterparty != playerindex {
                let mut deltasbuf = vec![];
                for kk in 0..inputs.len() {
                    deltasbuf.extend_from_slice(&betas[kk].sub(&shares[kk].0).to_bytes());
                }
                sendi.as_mut().unwrap().write(&deltasbuf)?;
                sendi.as_mut().unwrap().flush()?;
            }

            Ok(())
        })
        .collect::<Result<Vec<()>, Box<dyn Error>>>()
        .unwrap();

    let resultvec = recv[thislevelbase..(thislevelbase + thislevelparties)]
        .iter_mut() //par_iter_mut
        .zip(shares[thislevelbase..(thislevelbase + thislevelparties)].iter()) //par_iter
        .enumerate()
        .map(|(jj, (recvi, shares))| {
            let counterparty = thislevelbase + jj;

            let mut roundoutputaccumulator = vec![Scalar::zero(curve); inputs.len()];

            if counterparty != playerindex {
                let mut deltasbuf = vec![0u8; fr_bytes * inputs.len()];
                recvi.as_mut().unwrap().read_exact(&mut deltasbuf)?;

                for kk in 0..inputs.len() {
                    roundoutputaccumulator[kk] = shares[kk].1.add(
                        &Scalar::from_bytes(
                            curve,
                            &deltasbuf[(kk * fr_bytes)..((kk + 1) * fr_bytes)],
                        )
                        .mul(if counterparty < discriminator {
                            // I am Bob
                            &betas[kk]
                        } else {
                            // I am Alice
                            &shares[kk].0
                        }),
                    );
                }
            }

            Ok(roundoutputaccumulator)
        })
        .collect::<Result<Vec<Vec<Scalar>>, Box<dyn Error>>>()
        .unwrap();

    if thislevelparties > 0 {
        betas = vec![Scalar::zero(curve); inputs.len()];
        for thisresult in resultvec {
            for kk in 0..inputs.len() {
                betas[kk] = betas[kk].add(&thisresult[kk]);
            }
        }
    }

    betas
}

pub fn mpmul_first<TW: Write + std::marker::Send>(
    curve: &'static Curve,
    inputs: &[Scalar],
    playerindex: usize,
    shares: &[&[Scalar]],
    send: &mut [&mut Option<TW>],
) -> Result<(), Box<dyn Error>> {
    let playercount = send.len();

    let thislevel = (playerindex >> 1) << 1;
    let discriminator = thislevel + 1;
    let thislevelbase = if playerindex < discriminator {
        min(discriminator, playercount)
    } else {
        thislevel
    };
    let thislevelparties = min(playercount - thislevelbase, 1);

    send[thislevelbase..(thislevelbase + thislevelparties)]
        .iter_mut()
        .zip(shares[thislevelbase..(thislevelbase + thislevelparties)].iter())
        .enumerate()
        .map(|(jj, (sendi, shares))| {
            let counterparty = thislevelbase + jj;

            if counterparty != playerindex {
                let mut deltasbuf = vec![];
                for kk in 0..inputs.len() {
                    deltasbuf.extend_from_slice(&inputs[kk].sub(&shares[kk]).to_bytes());
                }
                sendi.as_mut().unwrap().write(&deltasbuf)?;
                sendi.as_mut().unwrap().flush()?;
            }

            Ok(())
        })
        .collect::<Result<Vec<()>, Box<dyn Error>>>()?;

    Ok(())
}

pub fn mpmul_rest<TR: Read + std::marker::Send, TW: Write + std::marker::Send>(
    curve: &'static Curve,
    inputs: &[Scalar],
    playerindex: usize,
    shares: &[&[(Scalar, Scalar)]],
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
) -> Result<Vec<Scalar>, Box<dyn Error>> {
    let fr_bytes = curve.fr_bytes;
    assert_eq!(recv.len(), send.len());

    let playercount = recv.len();
    let levels = (size_of_val(&playercount) * 8) - (playercount.leading_zeros() as usize) - 1;
    let levels = if playercount > (1 << levels) {
        levels + 1
    } else {
        levels
    };

    let mut betas = inputs.to_vec();

    let thislevel = (playerindex >> 1) << 1;
    let discriminator = thislevel + 1;
    let thislevelbase = if playerindex < discriminator {
        min(discriminator, playercount)
    } else {
        thislevel
    };
    let thislevelparties = min(playercount - thislevelbase, 1);

    let resultvec = recv[thislevelbase..(thislevelbase + thislevelparties)]
        .iter_mut() //par_iter_mut
        .zip(shares[thislevelbase..(thislevelbase + thislevelparties)].iter()) //par_iter
        .enumerate()
        .map(|(jj, (recvi, shares))| {
            let counterparty = thislevelbase + jj;

            let mut roundoutputaccumulator = vec![Scalar::zero(curve); inputs.len()];

            if counterparty != playerindex {
                let mut deltasbuf = vec![0u8; fr_bytes * inputs.len()];
                recvi.as_mut().unwrap().read_exact(&mut deltasbuf)?;

                for kk in 0..inputs.len() {
                    roundoutputaccumulator[kk] = shares[kk].1.add(
                        &Scalar::from_bytes(
                            curve,
                            &deltasbuf[(kk * fr_bytes)..((kk + 1) * fr_bytes)],
                        )
                        .mul(if counterparty < discriminator {
                            // I am Bob
                            &betas[kk]
                        } else {
                            // I am Alice
                            &shares[kk].0
                        }),
                    );
                }
            }

            Ok(roundoutputaccumulator)
        })
        .collect::<Result<Vec<Vec<Scalar>>, Box<dyn Error>>>()?;

    if thislevelparties > 0 {
        betas = vec![Scalar::zero(curve); inputs.len()];
        for thisresult in resultvec {
            for kk in 0..inputs.len() {
                betas[kk] = betas[kk].add(&thisresult[kk]);
            }
        }
    }

    for ii in 2..(levels + 1) {
        betas = mpmul_round(curve, ii, &betas, playerindex, shares, recv, send);
    }

    return Ok(betas);
}

pub fn mpmul<TR: Read + std::marker::Send, TW: Write + std::marker::Send>(
    curve: &'static Curve,
    inputs: &[Scalar],
    playerindex: usize,
    shares: &[&[(Scalar, Scalar)]],
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
) -> Vec<Scalar> {
    let playercount = recv.len();
    let levels = (size_of_val(&playercount) * 8) - (playercount.leading_zeros() as usize) - 1;
    let levels = if playercount > (1 << levels) {
        levels + 1
    } else {
        levels
    };

    let mut betas = inputs.to_vec();

    for ii in 1..(levels + 1) {
        betas = mpmul_round(curve, ii, &betas, playerindex, shares, recv, send);
    }

    betas
}

pub fn mpswapmul_send<TW: Write + std::marker::Send>(
    curve: &'static Curve,
    inputs: &[(Scalar, Scalar)],
    playerindex: usize,
    shares: &[&[(Scalar, Scalar)]],
    send: &mut [&mut Option<TW>],
) {
    send.iter_mut() //par_iter_mut
        .zip(shares.iter()) //par_iter
        .enumerate()
        .map(|(jj, (sendi, shares))| {
            let counterparty = jj;

            if counterparty != playerindex {
                let mut deltasbuf = vec![];
                for kk in 0..inputs.len() {
                    if counterparty < playerindex {
                        // I am Bob
                        deltasbuf
                            .extend_from_slice(&inputs[kk].0.sub(&shares[kk * 2].0).to_bytes());
                        deltasbuf
                            .extend_from_slice(&inputs[kk].1.sub(&shares[kk * 2 + 1].0).to_bytes());
                    } else if counterparty > playerindex {
                        // I am Alice
                        deltasbuf
                            .extend_from_slice(&inputs[kk].1.sub(&shares[kk * 2].0).to_bytes());
                        deltasbuf
                            .extend_from_slice(&inputs[kk].0.sub(&shares[kk * 2 + 1].0).to_bytes());
                    }
                }
                sendi.as_mut().unwrap().write(&deltasbuf)?;
            }

            Ok(())
        })
        .collect::<Result<Vec<()>, Box<dyn Error>>>()
        .unwrap();
}

pub fn mpswapmul_recv<TR: Read + std::marker::Send>(
    curve: &'static Curve,
    inputs: &[(Scalar, Scalar)],
    playerindex: usize,
    shares: &[&[(Scalar, Scalar)]],
    recv: &mut [&mut Option<TR>],
) -> Vec<Scalar> {
    let fr_bytes = curve.fr_bytes;
    let resultvec = recv
        .iter_mut() //part_iter_mut
        .zip(shares.iter()) //par_iter
        .enumerate()
        .map(|(jj, (recvi, shares))| {
            let counterparty = jj;

            Ok(if counterparty != playerindex {
                let mut deltasbuf = vec![0u8; fr_bytes * 2 * inputs.len()];
                recvi.as_mut().unwrap().read_exact(&mut deltasbuf)?;

                (0..inputs.len())
                    .map(|kk| {
                        shares[kk * 2]
                            .1
                            .add(
                                &Scalar::from_bytes(
                                    curve,
                                    &deltasbuf[(2 * kk * fr_bytes)..((2 * kk + 1) * fr_bytes)],
                                )
                                .mul(
                                    if counterparty < playerindex {
                                        // I am Bob
                                        &inputs[kk].0
                                    } else {
                                        // I am Alice
                                        &shares[kk * 2].0
                                    },
                                ),
                            )
                            .add(
                                &shares[kk * 2 + 1].1.add(
                                    &Scalar::from_bytes(
                                        curve,
                                        &deltasbuf
                                            [((2 * kk + 1) * fr_bytes)..((2 * kk + 2) * fr_bytes)],
                                    )
                                    .mul(
                                        if counterparty < playerindex {
                                            // I am Bob
                                            &inputs[kk].1
                                        } else {
                                            // I am Alice
                                            &shares[kk * 2 + 1].0
                                        },
                                    ),
                                ),
                            )
                    })
                    .collect()
            } else {
                inputs.iter().map(|(a, b)| a.mul(b)).collect()
            })
        })
        .collect::<Result<Vec<Vec<_>>, Box<dyn Error>>>()
        .unwrap();

    let mut sums = vec![Scalar::zero(curve); inputs.len()];
    for result in resultvec {
        for kk in 0..inputs.len() {
            sums[kk] = sums[kk].add(&result[kk]);
        }
    }

    sums
}

pub fn mpswapmul<TR: Read + std::marker::Send, TW: Write + std::marker::Send>(
    curve: &'static Curve,
    inputs: &[(Scalar, Scalar)],
    playerindex: usize,
    shares: &[&[(Scalar, Scalar)]],
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
) -> Vec<Scalar> {
    mpswapmul_send(curve, inputs, playerindex, shares, send);
    mpswapmul_recv(curve, inputs, playerindex, shares, recv)
}

pub enum RmulData {
    Sender(RmulSenderData),
    Recver(RmulRecverData),
}

pub fn mprmul_round_one<TR: Read + std::marker::Send, TW: Write + std::marker::Send, R: Rng>(
    curve: &'static Curve,
    mulcount: usize,
    playerindex: usize,
    multiplier: &mut [&mul::MulPlayer],
    ro: &GroupROTagger,
    rng: &mut R,
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
    rayonpool: &ThreadPool,
) -> Vec<(Vec<Scalar>, Option<RmulData>)> {
    assert_eq!(recv.len(), send.len());
    let playercount = recv.len();

    let mut rngs = Vec::with_capacity(playercount);
    let mut dros = Vec::with_capacity(playercount);
    for ii in 0..playercount {
        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
        dros.push(ro.get_dyadic_tagger(ii));
    }

    rayonpool.install(|| {
        send.par_iter_mut()
            .zip(recv.par_iter_mut())
            .zip(multiplier.par_iter_mut())
            .zip(dros.par_iter_mut())
            .zip(rngs.par_iter_mut())
            .enumerate()
            .map(|(jj, ((((sendi, recvi), thismultiplier), dro), rngi))| {
                let counterparty = jj;
                if counterparty < playerindex {
                    // I am Bob
                    let thismultiplier = match thismultiplier {
                        MulPlayer::Recver(ref thismultiplier) => thismultiplier,
                        _ => {
                            panic!()
                        }
                    };

                    let extensions = thismultiplier
                        .rmul_encode_and_extend(mulcount, dro, rngi, sendi.as_mut().unwrap())
                        .unwrap();
                    sendi.as_mut().unwrap().flush().unwrap();
                    (extensions.4.to_vec(), Some(RmulData::Recver(extensions)))
                } else if counterparty > playerindex {
                    // I am Alice
                    let thismultiplier = match thismultiplier {
                        MulPlayer::Sender(ref thismultiplier) => thismultiplier,
                        _ => {
                            panic!()
                        }
                    };

                    let extensions = thismultiplier
                        .rmul_extend(mulcount, dro, rngi, recvi.as_mut().unwrap())
                        .unwrap();
                    (extensions.2.to_vec(), Some(RmulData::Sender(extensions)))
                } else {
                    // I am Me
                    (Vec::with_capacity(0), None)
                }
            })
            .collect()
    })
}

pub fn mprmul_round_two<TR: Read + std::marker::Send, TW: Write + std::marker::Send, R: Rng>(
    curve: &'static Curve,
    playerindex: usize,
    round_one_data: &Vec<(Vec<Scalar>, Option<RmulData>)>,
    multiplier: &mut [&mul::MulPlayer],
    ro: &GroupROTagger,
    rng: &mut R,
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
    rayonpool: &ThreadPool,
    auxsend: Option<Vec<Vec<u8>>>,
) -> Vec<Vec<Scalar>> {
    assert_eq!(recv.len(), send.len());
    let playercount = recv.len();

    let mut rngs = Vec::with_capacity(playercount);
    let mut dros = Vec::with_capacity(playercount);
    for ii in 0..playercount {
        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
        dros.push(ro.get_dyadic_tagger(ii));
    }

    let auxsend = auxsend.unwrap_or(vec![Vec::new(); recv.len()]);

    rayonpool.install(|| {
        send.par_iter_mut()
            .zip(recv.par_iter_mut())
            .zip(multiplier.par_iter_mut())
            .zip(dros.par_iter_mut())
            .zip(rngs.par_iter_mut())
            .zip(round_one_data.par_iter())
            .zip(auxsend.par_iter())
            .enumerate()
            .map(
                |(
                    jj,
                    (
                        (((((sendi, recvi), thismultiplier), dro), rngi), round_one_datum),
                        auxsend_datum,
                    ),
                )| {
                    let counterparty = jj;
                    if counterparty < playerindex {
                        // I am Bob
                        let thismultiplier = match thismultiplier {
                            MulPlayer::Recver(ref thismultiplier) => thismultiplier,
                            _ => {
                                panic!()
                            }
                        };

                        let extensions = match round_one_datum {
                            (_, Some(RmulData::Recver(round_one_datum))) => round_one_datum,
                            _ => {
                                panic!()
                            }
                        };

                        sendi.as_mut().unwrap().write(&auxsend_datum).unwrap();
                        sendi.as_mut().unwrap().flush().unwrap();
                        let output = thismultiplier
                            .rmul_transfer(
                                &extensions.0,
                                &extensions.1,
                                &extensions.2,
                                &extensions.3,
                                dro,
                                recvi.as_mut().unwrap(),
                            )
                            .unwrap();
                        output
                    } else if counterparty > playerindex {
                        // I am Alice
                        let thismultiplier = match thismultiplier {
                            MulPlayer::Sender(ref thismultiplier) => thismultiplier,
                            _ => {
                                panic!()
                            }
                        };

                        let extensions = match round_one_datum {
                            (_, Some(RmulData::Sender(round_one_datum))) => round_one_datum,
                            _ => {
                                panic!()
                            }
                        };

                        let output = thismultiplier
                            .rmul_transfer(
                                &extensions.2.iter().collect::<Vec<_>>(),
                                &extensions.0,
                                &extensions.1,
                                dro,
                                rngi,
                                sendi.as_mut().unwrap(),
                            )
                            .unwrap();
                        sendi.as_mut().unwrap().write(&auxsend_datum).unwrap();
                        sendi.as_mut().unwrap().flush().unwrap();
                        output
                    } else {
                        // I am Me
                        Vec::with_capacity(0)
                    }
                },
            )
            .collect()
    })
}

pub fn mprmul<TR: Read + std::marker::Send, TW: Write + std::marker::Send, R: Rng>(
    curve: &'static Curve,
    mulcount: usize,
    playerindex: usize,
    multiplier: &mut [&mul::MulPlayer],
    ro: &GroupROTagger,
    rng: &mut R,
    recv: &mut [&mut Option<TR>],
    send: &mut [&mut Option<TW>],
    rayonpool: &ThreadPool,
) -> Vec<Vec<(Scalar, Scalar)>> {
    let r1d = mprmul_round_one(
        curve,
        mulcount,
        playerindex,
        multiplier,
        ro,
        rng,
        recv,
        send,
        rayonpool,
    );
    let r2d = mprmul_round_two(
        curve,
        playerindex,
        &r1d,
        multiplier,
        ro,
        rng,
        recv,
        send,
        rayonpool,
        None,
    );

    r1d.into_iter()
        .zip(r2d.into_iter())
        .map(|(r1datum, r2datum)| r1datum.0.into_iter().zip(r2datum.into_iter()).collect())
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::utils::P521;

    use super::channelstream::*;
    use super::*;
    use rand::RngCore;
    use std::env;
    use std::thread;
    use test::Bencher;

    #[test]
    fn test_mpmul_mpmul_7p_dual() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let parties = 7;

        let mut inputproducts = vec![Scalar::one(curve); 2];

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                let input0 = curve.rand_scalar(&mut rng);
                let input1 = curve.rand_scalar(&mut rng);
                inputproducts[0] = inputproducts[0].mul(&input0);
                inputproducts[1] = inputproducts[1].mul(&input1);

                thread::spawn(move || {
                    let mut sin = si;
                    let mut rin = ri;

                    let mut rng = rand::thread_rng();
                    let mut rngs = Vec::with_capacity(parties);
                    for _ in 0..parties {
                        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
                    }

                    let mut ro = {
                        let mut riref = rin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        let mut siref = sin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        GroupROTagger::from_network_unverified(
                            ii,
                            &mut rng,
                            &mut riref[..],
                            &mut siref[..],
                        )
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(parties)
                        .build()
                        .unwrap();
                    let multipliervec = rayonpool.install(|| {
                        sin.par_iter_mut()
                            .zip(rin.par_iter_mut())
                            .zip(rngs.par_iter_mut())
                            .enumerate()
                            .map(|(jj, ((sendi, recvi), rngi))| {
                                if jj > ii {
                                    MulPlayer::Sender(mul::MulSender::new(
                                        curve,
                                        &ro.get_dyadic_tagger(jj),
                                        rngi,
                                        recvi.as_mut().unwrap(),
                                        sendi.as_mut().unwrap(),
                                    ))
                                } else if jj < ii {
                                    MulPlayer::Recver(
                                        mul::MulRecver::new(
                                            curve,
                                            &ro.get_dyadic_tagger(jj),
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
                            .collect::<Vec<_>>()
                    });

                    let mut multiplierrefvec = multipliervec.iter().collect::<Vec<_>>();
                    let mut sendrefvec: Vec<&mut Option<_>> = sin.iter_mut().collect();
                    let mut recvrefvec: Vec<&mut Option<_>> = rin.iter_mut().collect();

                    let threadcount = match env::var_os("RAYON_NUM_THREADS") {
                        Some(val) => val.into_string().unwrap().parse().unwrap(),
                        None => parties,
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(threadcount)
                        .build()
                        .unwrap();

                    ro.apply_subgroup_list(&(0..parties).collect::<Vec<usize>>())
                        .unwrap();

                    let shares = mprmul(
                        curve,
                        2,
                        ii,
                        multiplierrefvec.as_mut_slice(),
                        &ro,
                        &mut rng,
                        recvrefvec.as_mut_slice(),
                        sendrefvec.as_mut_slice(),
                        &rayonpool,
                    );
                    let mut shares1 = Vec::with_capacity(shares.len());
                    for kk in 0..shares.len() {
                        shares1.push(&shares[kk][..]);
                    }
                    mpmul(
                        curve,
                        &[input0, input1],
                        ii,
                        shares1.as_slice(),
                        recvrefvec.as_mut_slice(),
                        sendrefvec.as_mut_slice(),
                    )
                })
            })
            .collect::<Vec<_>>();

        let mut outputsums = vec![Scalar::zero(curve); 2];
        for handle in thandles {
            let output = handle.join().unwrap();
            outputsums[0] = outputsums[0].add(&output[0]);
            outputsums[1] = outputsums[1].add(&output[1]);
        }

        assert_eq!(outputsums[0], inputproducts[0]);
        assert_eq!(outputsums[1], inputproducts[1]);
    }

    #[test]
    fn test_mpmul_mpflatmul_7p() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let parties = 7;

        let mut inputsums = vec![Scalar::zero(curve); 2];

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                let input0 = curve.rand_scalar(&mut rng);
                let input1 = curve.rand_scalar(&mut rng);
                inputsums[0] = inputsums[0].add(&input0);
                inputsums[1] = inputsums[1].add(&input1);

                thread::spawn(move || {
                    let mut sin = si;
                    let mut rin = ri;

                    let mut rng = rand::thread_rng();
                    let mut rngs = Vec::with_capacity(parties);
                    for _ in 0..parties {
                        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
                    }

                    let mut ro = {
                        let mut riref = rin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        let mut siref = sin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        GroupROTagger::from_network_unverified(
                            ii,
                            &mut rng,
                            &mut riref[..],
                            &mut siref[..],
                        )
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(parties)
                        .build()
                        .unwrap();
                    let multipliervec = rayonpool.install(|| {
                        sin.par_iter_mut()
                            .zip(rin.par_iter_mut())
                            .zip(rngs.par_iter_mut())
                            .enumerate()
                            .map(|(jj, ((sendi, recvi), rngi))| {
                                if jj > ii {
                                    MulPlayer::Sender(mul::MulSender::new(
                                        curve,
                                        &ro.get_dyadic_tagger(jj),
                                        rngi,
                                        recvi.as_mut().unwrap(),
                                        sendi.as_mut().unwrap(),
                                    ))
                                } else if jj < ii {
                                    MulPlayer::Recver(
                                        mul::MulRecver::new(
                                            curve,
                                            &ro.get_dyadic_tagger(jj),
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
                            .collect::<Vec<_>>()
                    });

                    let mut multiplierrefvec = multipliervec.iter().collect::<Vec<_>>();
                    let mut sendrefvec: Vec<&mut Option<_>> = sin.iter_mut().collect();
                    let mut recvrefvec: Vec<&mut Option<_>> = rin.iter_mut().collect();

                    let threadcount = match env::var_os("RAYON_NUM_THREADS") {
                        Some(val) => val.into_string().unwrap().parse().unwrap(),
                        None => parties,
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(threadcount)
                        .build()
                        .unwrap();

                    ro.apply_subgroup_list(&(0..parties).collect::<Vec<usize>>());

                    let shares = mprmul(
                        curve,
                        2,
                        ii,
                        multiplierrefvec.as_mut_slice(),
                        &ro,
                        &mut rng,
                        recvrefvec.as_mut_slice(),
                        sendrefvec.as_mut_slice(),
                        &rayonpool,
                    );
                    let mut shares1 = Vec::with_capacity(shares.len());
                    for kk in 0..shares.len() {
                        shares1.push(&shares[kk][..]);
                    }
                    mpswapmul_send(
                        curve,
                        &[(input0.clone(), input1.clone())],
                        ii,
                        shares1.as_slice(),
                        sendrefvec.as_mut_slice(),
                    );
                    mpswapmul_recv(
                        curve,
                        &[(input0, input1)],
                        ii,
                        shares1.as_slice(),
                        recvrefvec.as_mut_slice(),
                    )
                })
            })
            .collect::<Vec<_>>();

        let mut outputsum = Scalar::zero(curve);
        for handle in thandles {
            let output = handle.join().unwrap();
            outputsum = outputsum.add(&output[0]);
        }

        assert_eq!(outputsum, inputsums[0].mul(&inputsums[1]));
    }

    #[test]
    fn test_mpmul_mpmul_4p_quintuple() {
        let curve = &P521;
        let mut rng = rand::thread_rng();
        let parties = 4;

        let mut inputproducts = vec![Scalar::one(curve); 5];

        let (sendvec, recvvec) = spawn_n2_channelstreams(parties);

        let thandles = sendvec
            .into_iter()
            .zip(recvvec.into_iter())
            .enumerate()
            .map(|(ii, (si, ri))| {
                let input0 = curve.rand_scalar(&mut rng);
                let input1 = curve.rand_scalar(&mut rng);
                let input2 = curve.rand_scalar(&mut rng);
                let input3 = curve.rand_scalar(&mut rng);
                let input4 = curve.rand_scalar(&mut rng);
                inputproducts[0] = inputproducts[0].mul(&input0);
                inputproducts[1] = inputproducts[1].mul(&input1);
                inputproducts[2] = inputproducts[2].mul(&input2);
                inputproducts[3] = inputproducts[3].mul(&input3);
                inputproducts[4] = inputproducts[4].mul(&input4);

                thread::spawn(move || {
                    let mut sin = si;
                    let mut rin = ri;

                    let mut rng = rand::thread_rng();
                    let mut rngs = Vec::with_capacity(parties);
                    for _ in 0..parties {
                        rngs.push(ChaChaRng::seed_from_u64(rng.next_u64()));
                    }

                    let mut ro = {
                        let mut riref = rin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        let mut siref = sin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        GroupROTagger::from_network_unverified(
                            ii,
                            &mut rng,
                            &mut riref[..],
                            &mut siref[..],
                        )
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(parties)
                        .build()
                        .unwrap();
                    let multipliervec = rayonpool.install(|| {
                        sin.par_iter_mut()
                            .zip(rin.par_iter_mut())
                            .zip(rngs.par_iter_mut())
                            .enumerate()
                            .map(|(jj, ((sendi, recvi), rngi))| {
                                if jj > ii {
                                    MulPlayer::Sender(mul::MulSender::new(
                                        curve,
                                        &ro.get_dyadic_tagger(jj),
                                        rngi,
                                        recvi.as_mut().unwrap(),
                                        sendi.as_mut().unwrap(),
                                    ))
                                } else if jj < ii {
                                    MulPlayer::Recver(
                                        mul::MulRecver::new(
                                            curve,
                                            &ro.get_dyadic_tagger(jj),
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
                            .collect::<Vec<_>>()
                    });

                    let mut multiplierrefvec = multipliervec.iter().collect::<Vec<_>>();
                    let mut sendrefvec: Vec<&mut Option<_>> = sin.iter_mut().collect();
                    let mut recvrefvec: Vec<&mut Option<_>> = rin.iter_mut().collect();

                    let threadcount = match env::var_os("RAYON_NUM_THREADS") {
                        Some(val) => val.into_string().unwrap().parse().unwrap(),
                        None => parties,
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(threadcount)
                        .build()
                        .unwrap();

                    ro.apply_subgroup_list(&(0..parties).collect::<Vec<usize>>());

                    let shares = mprmul(
                        curve,
                        5,
                        ii,
                        multiplierrefvec.as_mut_slice(),
                        &ro,
                        &mut rng,
                        recvrefvec.as_mut_slice(),
                        sendrefvec.as_mut_slice(),
                        &rayonpool,
                    );
                    let mut shares1 = Vec::with_capacity(shares.len());
                    for kk in 0..shares.len() {
                        shares1.push(&shares[kk][..]);
                    }
                    mpmul(
                        curve,
                        &[input0, input1, input2, input3, input4],
                        ii,
                        shares1.as_slice(),
                        recvrefvec.as_mut_slice(),
                        sendrefvec.as_mut_slice(),
                    )
                })
            })
            .collect::<Vec<_>>();

        let mut outputsums = vec![Scalar::zero(curve); 5];
        for handle in thandles {
            let output = handle.join().unwrap();
            outputsums[0] = outputsums[0].add(&output[0]);
            outputsums[1] = outputsums[1].add(&output[1]);
            outputsums[2] = outputsums[2].add(&output[2]);
            outputsums[3] = outputsums[3].add(&output[3]);
            outputsums[4] = outputsums[4].add(&output[4]);
        }

        assert_eq!(outputsums[0], inputproducts[0]);
        assert_eq!(outputsums[1], inputproducts[1]);
        assert_eq!(outputsums[2], inputproducts[2]);
        assert_eq!(outputsums[3], inputproducts[3]);
        assert_eq!(outputsums[4], inputproducts[4]);
    }

    #[bench]
    fn bench_mpmul_mpmul_7p_dual(b: &mut Bencher) {
        let curve = &P521;
        let parties = 7;

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

                    let mut ro = {
                        let mut riref = rin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        let mut siref = sin
                            .iter_mut()
                            .map(|x| if x.is_some() { x.as_mut() } else { None })
                            .collect::<Vec<Option<&mut _>>>();
                        GroupROTagger::from_network_unverified(
                            ii,
                            &mut rng,
                            &mut riref[..],
                            &mut siref[..],
                        )
                    };

                    let rayonpool = rayon::ThreadPoolBuilder::new()
                        .num_threads(parties)
                        .build()
                        .unwrap();
                    let multipliervec = rayonpool.install(|| {
                        sin.par_iter_mut()
                            .zip(rin.par_iter_mut())
                            .zip(rngs.par_iter_mut())
                            .enumerate()
                            .map(|(jj, ((sendi, recvi), rngi))| {
                                if jj > ii {
                                    MulPlayer::Sender(mul::MulSender::new(
                                        curve,
                                        &ro.get_dyadic_tagger(jj),
                                        rngi,
                                        recvi.as_mut().unwrap(),
                                        sendi.as_mut().unwrap(),
                                    ))
                                } else if jj < ii {
                                    MulPlayer::Recver(
                                        mul::MulRecver::new(
                                            curve,
                                            &ro.get_dyadic_tagger(jj),
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
                            .collect::<Vec<_>>()
                    });

                    let mut multiplierrefvec = multipliervec.iter().collect::<Vec<_>>();
                    let mut sendrefvec: Vec<&mut Option<_>> = sin.iter_mut().collect();
                    let mut recvrefvec: Vec<&mut Option<_>> = rin.iter_mut().collect();

                    ro.apply_subgroup_list(&(0..parties).collect::<Vec<usize>>())
                        .unwrap();

                    let mut keepgoing = [1u8; 1];
                    recvrefvec[0]
                        .as_mut()
                        .unwrap()
                        .read_exact(&mut keepgoing)
                        .expect(&format!("Party {} failed to read (1)", ii));
                    while keepgoing[0] > 0 {
                        let input0 = curve.rand_scalar(&mut rng);
                        let input1 = curve.rand_scalar(&mut rng);
                        let shares = mprmul(
                            curve,
                            2,
                            ii,
                            multiplierrefvec.as_mut_slice(),
                            &ro,
                            &mut rng,
                            recvrefvec.as_mut_slice(),
                            sendrefvec.as_mut_slice(),
                            &rayonpool,
                        );
                        let mut shares1 = Vec::with_capacity(shares.len());
                        for kk in 0..shares.len() {
                            shares1.push(&shares[kk][..]);
                        }
                        mpmul(
                            curve,
                            &[input0, input1],
                            ii,
                            shares1.as_slice(),
                            recvrefvec.as_mut_slice(),
                            sendrefvec.as_mut_slice(),
                        );
                        recvrefvec[0]
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

        let mut ro = {
            let mut r0ref = r0
                .iter_mut()
                .map(|x| if x.is_some() { x.as_mut() } else { None })
                .collect::<Vec<Option<&mut _>>>();
            let mut s0ref = s0
                .iter_mut()
                .map(|x| if x.is_some() { x.as_mut() } else { None })
                .collect::<Vec<Option<&mut _>>>();
            GroupROTagger::from_network_unverified(0, &mut rng, &mut r0ref[..], &mut s0ref[..])
        };

        let rayonpool = rayon::ThreadPoolBuilder::new()
            .num_threads(parties)
            .build()
            .unwrap();
        let multipliervec = rayonpool.install(|| {
            s0.par_iter_mut()
                .zip(r0.par_iter_mut())
                .zip(rngs.par_iter_mut())
                .enumerate()
                .map(|(jj, ((sendi, recvi), rngi))| {
                    if jj > 0 {
                        MulPlayer::Sender(mul::MulSender::new(
                            curve,
                            &ro.get_dyadic_tagger(jj),
                            rngi,
                            recvi.as_mut().unwrap(),
                            sendi.as_mut().unwrap(),
                        ))
                    } else {
                        MulPlayer::Null
                    }
                })
                .collect::<Vec<_>>()
        });

        let mut multiplierrefvec = multipliervec.iter().collect::<Vec<_>>();
        let mut sendrefvec: Vec<&mut Option<_>> = s0.iter_mut().collect();
        let mut recvrefvec: Vec<&mut Option<_>> = r0.iter_mut().collect();

        ro.apply_subgroup_list(&(0..parties).collect::<Vec<usize>>())
            .unwrap();

        b.iter(|| {
            for ii in 1..parties {
                sendrefvec[ii]
                    .as_mut()
                    .unwrap()
                    .write(&[1])
                    .expect("Party 0 failed to write (1)");
                sendrefvec[ii]
                    .as_mut()
                    .unwrap()
                    .flush()
                    .expect("Party 0 failed to flush");
            }
            let input0 = curve.rand_scalar(&mut rng);
            let input1 = curve.rand_scalar(&mut rng);

            let threadcount = match env::var_os("RAYON_NUM_THREADS") {
                Some(val) => val.into_string().unwrap().parse().unwrap(),
                None => parties,
            };

            let rayonpool = rayon::ThreadPoolBuilder::new()
                .num_threads(threadcount)
                .build()
                .unwrap();

            let shares = mprmul(
                curve,
                2,
                0,
                multiplierrefvec.as_mut_slice(),
                &ro,
                &mut rng,
                recvrefvec.as_mut_slice(),
                sendrefvec.as_mut_slice(),
                &rayonpool,
            );
            let mut shares1 = Vec::with_capacity(shares.len());
            for kk in 0..shares.len() {
                shares1.push(&shares[kk][..]);
            }
            mpmul(
                curve,
                &[input0, input1],
                0,
                shares1.as_slice(),
                recvrefvec.as_mut_slice(),
                sendrefvec.as_mut_slice(),
            );
        });

        for ii in 1..parties {
            sendrefvec[ii]
                .as_mut()
                .unwrap()
                .write(&[0])
                .expect("Party 0 failed to write (2)");
            sendrefvec[ii]
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
