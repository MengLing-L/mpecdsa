#![feature(test)]
#![feature(slice_as_chunks)]
#![feature(generic_const_exprs)]

pub mod channelstream;
pub mod mpecdsa; // threshold ECDSA
pub mod mpmul; // multiparty multiplication
pub mod mul; // two-party multiplication
pub mod ote; // OT extension
pub mod ro; // random oracle
pub mod rot; // random OT
pub mod utils;
pub mod zkpok; // zero knowledge proofs (incl NIZK) // mock networking for testing

use std::io;
use std::io::prelude::*;

extern crate bit_reverse;
extern crate byteorder;
extern crate core;
extern crate rand;
extern crate rayon;
extern crate test;
#[macro_use]
extern crate lazy_static;

use rayon::{slice::ParallelSlice, prelude::ParallelIterator};
use sha2::{Digest, Sha256, Sha384, Sha512};

extern crate hex;

/* The hash size is essentially a security parameter.
Note that the hash algorithm must be changed with
the output size, so that they match. Note also that
the hash block size must be somewhat larger than
the hash output size, or things will break. This
should be done more intelligently in the future.
*/

const RO_TAG_SIZE: usize = 20; // Why 20? Because our vectorized SHA-256 impl takes only 52 = 32+20 bytes as input
pub const HASH_SIZE: usize = 66;
const HASH_BLOCK_SIZE: usize = RO_TAG_SIZE + HASH_SIZE;
// const ENCODING_PER_ELEMENT_BITS: usize = SecpOrd::NBITS + 160;
const ENCODING_EXTRA_BITS: usize = 0; // From IN96, this must be 2*s
// const RAND_ENCODING_PER_ELEMENT_BITS: usize = SecpOrd::NBITS + 160;
const RAND_ENCODING_EXTRA_BITS: usize = 0; // From IN96, this must be 2*s
const OT_SEC_PARAM: usize = 128 + 80; // From KOS, this should be 128+s

fn hash_multi(src: &[u8]) -> Vec<Vec<u8>> {
	src.par_chunks(HASH_BLOCK_SIZE).map(hash).collect()
}

fn hash(msg: &[u8]) -> Vec<u8> {
    let mut r = Sha512::digest(msg).to_vec();
	r.resize(HASH_SIZE, 0);
	r
}
