use std::error::Error;
use std::io::prelude::*;

use rand::Rng;

use crate::utils::{Curve, Point, Scalar};

use super::ro::*;
use super::*;

pub fn prove_dl_fs<T: Write, R: Rng>(
    curve: &'static Curve,
    x: &Scalar,
    gx: &Point,
    ro: &dyn ro::ModelessROTagger,
	rng: &mut R,
    send: &mut T,
) -> Result<(), Box<dyn Error>> {
    let (randcommitted, randcommitment) = curve.rand_scalar_and_point(rng);
    let randcommitment = randcommitment.to_bytes();
    let challenge = hash(&[ro.next_tag(), gx.to_bytes(), randcommitment.clone()].concat()); // TODO: tag
    let challenge = curve.parse_scalar(&challenge);

    let z = x.mul(&challenge).add(&randcommitted);

    send.write(&[randcommitment, z.to_bytes()].concat())?;
    Ok(())
}

pub fn verify_dl_fs<T: Read>(
    curve: &'static Curve,
    gx: &Point,
    ro: &ModelessDyadicROTagger,
    recv: &mut T,
) -> bool {
    let secp_bytes = curve.fq_bytes * 2 + 1;
    let fr_bytes = curve.fr_bytes;
    let mut buf = vec![0u8; 2 * secp_bytes + fr_bytes + RO_TAG_SIZE];
    buf[RO_TAG_SIZE..(secp_bytes + RO_TAG_SIZE)].copy_from_slice(&gx.to_bytes());

    buf[0..RO_TAG_SIZE].copy_from_slice(&ro.next_dyadic_counterparty_tag());

    recv.read_exact(&mut buf[(secp_bytes + RO_TAG_SIZE)..])
        .unwrap();
    let randcommitment = Point::from_bytes(
        curve,
        &buf[(secp_bytes + RO_TAG_SIZE)..(2 * secp_bytes + RO_TAG_SIZE)],
    );

    let challenge = hash(&buf[0..(2 * secp_bytes + RO_TAG_SIZE)]); // TODO: tag

    let gresp = Point::from_scalar(
        curve,
        &curve.parse_scalar(
            &buf[(2 * secp_bytes + RO_TAG_SIZE)..(2 * secp_bytes + fr_bytes + RO_TAG_SIZE)],
        ),
    );
    let gresp_exp = randcommitment.add(&gx.mul(&curve.parse_scalar(&challenge)));

    gresp == gresp_exp
}

pub fn prove_dl_fs_to_com<R: Rng>(
    curve: &'static Curve,
    x: &Scalar,
    gx: &Point,
    ro: &dyn ModelessROTagger,
	rng: &mut R,
) -> Result<(Vec<u8>, Vec<u8>), Box<dyn Error>> {
    let secp_bytes = curve.fq_bytes * 2 + 1;
    let fr_bytes = curve.fr_bytes;
    // write proof into a memory buffer
    let mut proof = std::io::Cursor::new(vec![0u8; fr_bytes + secp_bytes + RO_TAG_SIZE]);

    // we perform only local IO, so there should never be an error
    prove_dl_fs(curve, x, gx, ro, rng, &mut proof)?;

    let mut proof = proof.into_inner();
    proof[(fr_bytes + secp_bytes)..].copy_from_slice(&ro.next_tag());
    let mut com = hash(&proof);
    let mut proofout = vec![0u8; fr_bytes + secp_bytes];
    proofout.copy_from_slice(&proof[0..(fr_bytes + secp_bytes)]);
    Ok((com.into(), proofout))
}

pub fn verify_dl_fs_with_com<T: Read>(
    curve: &'static Curve,
    gx: &Point,
    proofcommitment: &[u8],
    ro: &ModelessDyadicROTagger,
    recv: &mut T,
) -> Result<bool, Box<dyn Error>> {
    let secp_bytes = curve.fq_bytes * 2 + 1;
    let fr_bytes = curve.fr_bytes;
    let mut buf = vec![0u8; 2 * secp_bytes + fr_bytes + RO_TAG_SIZE];
    buf[0..secp_bytes].copy_from_slice(&gx.to_bytes());

    recv.read_exact(&mut buf[secp_bytes..(2 * secp_bytes + fr_bytes)])?;

    let pass = {
        let mut proof = std::io::Cursor::new(&buf[secp_bytes..(2 * secp_bytes + fr_bytes)]);
        verify_dl_fs(curve, gx, ro, &mut proof)
    };

    buf[(2 * secp_bytes + fr_bytes)..].copy_from_slice(&ro.next_dyadic_counterparty_tag());

    let mut exp_commitment = hash(&buf[secp_bytes..(2 * secp_bytes + fr_bytes + RO_TAG_SIZE)]);

    Ok(pass && (proofcommitment == &exp_commitment))
}

pub fn verify_dl_fs_with_com_grouped<T: Read>(
    curve: &'static Curve,
    gx: &[Point],
    proofcommitment: &[Vec<u8>],
    counterparties: &[usize],
    ro: &dyn ModelessROTagger,
    recv: &mut [&mut Option<T>],
) -> Result<bool, Box<dyn Error>> {
    let secp_bytes = curve.fq_bytes * 2 + 1;
    let fr_bytes = curve.fr_bytes;
    let mut comspass = true;
    let mut randcommitment = Point::inf(curve);
    let mut gxc = Point::inf(curve);
    let mut z = Scalar::zero(&curve);
    for ii in 0..recv.len() {
        let mut buf = vec![0u8; 2 * secp_bytes + fr_bytes + 2 * RO_TAG_SIZE];
        if recv[ii].is_some() {
            recv[ii].as_mut().unwrap().read_exact(
                &mut buf[(RO_TAG_SIZE + secp_bytes)..(2 * secp_bytes + fr_bytes + RO_TAG_SIZE)],
            )?;

            randcommitment = randcommitment.add(&Point::from_bytes(
                curve,
                &buf[(secp_bytes + RO_TAG_SIZE)..(2 * secp_bytes + RO_TAG_SIZE)],
            ));

            let tag2 = ro.next_counterparty_tag(counterparties[ii]);
            buf[0..RO_TAG_SIZE].copy_from_slice(&tag2[..]);

            buf[RO_TAG_SIZE..(secp_bytes + RO_TAG_SIZE)].copy_from_slice(&gx[ii].to_bytes());

            let mut challenge = hash(&buf[0..2 * secp_bytes + RO_TAG_SIZE]); // TODO: tag

            let challenge = curve.parse_scalar(&challenge[..]);
            gxc = gxc.add(&gx[ii].mul(&challenge));
            z = z.add(&curve.parse_scalar(
                &buf[(2 * secp_bytes + RO_TAG_SIZE)..(2 * secp_bytes + fr_bytes + RO_TAG_SIZE)],
            ));

            buf[(2 * secp_bytes + fr_bytes + RO_TAG_SIZE)..]
                .copy_from_slice(&ro.next_counterparty_tag(counterparties[ii]));
            let mut exp_commitment = hash(
                &buf[(RO_TAG_SIZE + secp_bytes)..(2 * secp_bytes + fr_bytes + 2 * RO_TAG_SIZE)],
            ); // TODO: tag
            comspass = comspass && (proofcommitment[ii] == exp_commitment);
        }
    }

    let gresp = Point::from_scalar(curve, &z);
    let gresp_exp = gxc.add(&randcommitment);

    Ok((gresp == gresp_exp) && comspass)
}
