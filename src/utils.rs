use std::{
    fmt::Debug,
    io::Read,
    mem::MaybeUninit,
    sync::{Mutex, Once},
    time::Instant,
};

use openssl::{
    bn::{BigNum, BigNumContext},
    ec::{EcGroup, EcPoint, PointConversionForm},
    nid::Nid,
};
use rand::Rng;

pub struct Ctx {
    pub ctx: Mutex<BigNumContext>,
    pub k256: Curve,
    pub p384: Curve,
    pub p521: Curve,
}

lazy_static! {
    pub static ref CTX: BigNumContext = BigNumContext::new().unwrap();
    pub static ref K256: Curve = Curve::new(Nid::SECP256K1, 256, 256);
    pub static ref P384: Curve = Curve::new(Nid::SECP384R1, 384, 384);
    pub static ref P521: Curve = Curve::new(Nid::SECP521R1, 528, 528);
}

pub struct Curve {
    v: EcGroup,
    pub order: BigNum,
    pub fr_bits: usize,
    pub fr_bytes: usize,
    pub fq_bits: usize,
    pub fq_bytes: usize,
}

impl Curve {
    pub fn new(id: Nid, fr_bits: usize, fq_bits: usize) -> Self {
        let mut order = BigNum::new().unwrap();
        let v = EcGroup::from_curve_name(id).unwrap();
        v.order(&mut order, &mut BigNumContext::new().unwrap())
            .unwrap();
        Self {
            v,
            fr_bits,
            fr_bytes: (fr_bits + 7) / 8,
            fq_bits,
            fq_bytes: (fq_bits + 7) / 8,
            order,
        }
    }

    pub fn rand_scalar<R: Rng>(&'static self, _: &mut R) -> Scalar {
        let mut x = BigNum::new().unwrap();
        self.order.rand_range(&mut x).unwrap();
        Scalar { v: x, curve: self }
    }

    pub fn rand_scalar_and_point<R: Rng>(&'static self, _: &mut R) -> (Scalar, Point) {
        let mut x = BigNum::new().unwrap();
        self.order.rand_range(&mut x).unwrap();
        let scalar = Scalar { v: x, curve: self };
        let point = Point::from_scalar(self, &scalar);
        (scalar, point)
    }

    pub fn parse_scalar(&'static self, bytes: &[u8]) -> Scalar {
        Scalar::from_bytes(self, bytes)
    }

    pub fn parse_point(&'static self, bytes: &[u8]) -> Point {
        Point::from_bytes(self, bytes)
    }

    pub fn read_scalar<R: Read>(&'static self, reader: &mut R) -> Scalar {
        Scalar::from_reader(self, reader)
    }

    pub fn read_point<R: Read>(&'static self, reader: &mut R) -> Point {
        Point::from_reader(self, reader)
    }
}

pub struct Point {
    v: EcPoint,
    curve: &'static Curve,
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.v
            .eq(&self.curve.v, &other.v, &mut BigNumContext::new().unwrap())
            .unwrap()
    }
}

impl Point {
    pub fn from_scalar(curve: &'static Curve, scalar: &Scalar) -> Self {
        let mut point = EcPoint::new(&curve.v).unwrap();
        point
            .mul_generator(&curve.v, &scalar.v, &mut BigNumContext::new().unwrap())
            .unwrap();

        Self {
            v: point,
            curve: curve,
        }
    }

    pub fn from_bytes(curve: &'static Curve, bytes: &[u8]) -> Self {
        Self {
            v: EcPoint::from_bytes(&curve.v, &bytes, &mut BigNumContext::new().unwrap()).unwrap(),
            curve,
        }
    }

    pub fn from_reader<R: Read>(curve: &'static Curve, reader: &mut R) -> Self {
        let mut bytes = vec![0u8; curve.fq_bytes * 2 + 1];
        reader.read_exact(&mut bytes).unwrap();
        Self::from_bytes(curve, &bytes)
    }

    pub fn inf(curve: &'static Curve) -> Self {
        Self {
            v: EcPoint::new(&curve.v).unwrap(),
            curve,
        }
    }

    pub fn gen(curve: &'static Curve) -> Self {
        Self {
            v: curve.v.generator().to_owned(&curve.v).unwrap(),
            curve,
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.v
            .to_bytes(
                &self.curve.v,
                PointConversionForm::UNCOMPRESSED,
                &mut BigNumContext::new().unwrap(),
            )
            .unwrap()
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut point = Self::inf(self.curve);
        point
            .v
            .add(
                &self.curve.v,
                &self.v,
                &other.v,
                &mut BigNumContext::new().unwrap(),
            )
            .unwrap();
        point
    }

    pub fn mul(&self, scalar: &Scalar) -> Self {
        let mut point = Self::inf(self.curve);
        point
            .v
            .mul(
                &self.curve.v,
                &self.v,
                &scalar.v,
                &mut BigNumContext::new().unwrap(),
            )
            .unwrap();
        point
    }

    pub fn neg(&self) -> Self {
        let mut v = self.v.to_owned(&self.curve.v).unwrap();
        v.invert(&self.curve.v, &mut BigNumContext::new().unwrap())
            .unwrap();
        Self {
            v,
            curve: self.curve,
        }
    }

    pub fn x_bytes(&self) -> Vec<u8> {
        let mut x = BigNum::new().unwrap();
        let mut y = BigNum::new().unwrap();
        self.v
            .affine_coordinates(
                &self.curve.v,
                &mut x,
                &mut y,
                &mut BigNumContext::new().unwrap(),
            )
            .unwrap();
        x.to_vec_padded(self.curve.fq_bytes as i32).unwrap()
    }
}

impl Clone for Point {
    fn clone(&self) -> Self {
        Self {
            v: self.v.to_owned(&self.curve.v).unwrap(),
            curve: self.curve.clone(),
        }
    }
}

impl Debug for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Point({:?})", self.to_bytes())
    }
}
pub struct Scalar {
    v: BigNum,
    curve: &'static Curve,
}

impl Scalar {
    pub fn nnmod(&self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.nnmod(
            &self.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }

    pub fn from_bytes(curve: &'static Curve, bytes: &[u8]) -> Self {
        Self {
            v: BigNum::from_slice(&bytes).unwrap(),
            curve,
        }
    }

    pub fn from_reader<R: Read>(curve: &'static Curve, reader: &mut R) -> Self {
        let mut bytes = vec![0u8; curve.fr_bytes];
        reader.read_exact(&mut bytes).unwrap();
        Self::from_bytes(curve, &bytes)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.v.to_vec_padded(self.curve.fr_bytes as i32).unwrap()
    }

    pub fn zero(curve: &'static Curve) -> Self {
        Self {
            v: BigNum::new().unwrap(),
            curve,
        }
    }

    pub fn one(curve: &'static Curve) -> Self {
        Self {
            v: BigNum::from_u32(1).unwrap(),
            curve,
        }
    }

    pub fn from_u32(curve: &'static Curve, n: u32) -> Self {
        Self {
            v: BigNum::from_u32(n).unwrap(),
            curve,
        }
    }

    pub fn two_to_n(curve: &'static Curve, n: usize) -> Self {
        let mut r = Self::zero(curve);
        r.v.set_bit(n as i32).unwrap();
        r
    }

    pub fn bit(&self, n: usize) -> bool {
        self.v.is_bit_set(n as i32)
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.mod_add(
            &self.v,
            &other.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.mod_sub(
            &self.v,
            &other.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.mod_mul(
            &self.v,
            &other.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }

    pub fn sqr(&self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.mod_sqr(
            &self.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }

    pub fn neg(&self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.mod_sub(
            &self.curve.order,
            &self.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }

    pub fn inv(&self) -> Self {
        let mut x = BigNum::new().unwrap();
        x.mod_inverse(
            &self.v,
            &self.curve.order,
            &mut BigNumContext::new().unwrap(),
        )
        .unwrap();
        Self {
            v: x,
            curve: self.curve,
        }
    }
}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.v.eq(&other.v)
    }
}

impl Clone for Scalar {
    fn clone(&self) -> Self {
        Self {
            v: self.v.to_owned().unwrap(),
            curve: self.curve.clone(),
        }
    }
}

impl Debug for Scalar {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "Scalar({})", self.v.to_dec_str().unwrap())
    }
}


// use std::{
//     fmt::Debug,
//     io::Read,
//     mem::MaybeUninit,
//     sync::{Mutex, Once},
//     time::Instant,
// };

// use k256::elliptic_curve::{
//     generic_array::GenericArray,
//     ops::{Invert, Reduce},
//     PrimeField, group::GroupEncoding, AffineXCoordinate, sec1::{ToEncodedPoint, FromEncodedPoint}, Field,
// };
// use openssl::{
//     bn::{BigNum, BigNumContext},
//     ec::{EcGroup, EcPoint, PointConversionForm},
//     nid::Nid,
// };
// use rand::Rng;

// lazy_static! {
//     pub static ref CTX: BigNumContext = BigNumContext::new().unwrap();
//     pub static ref K256: Curve = Curve::new(Nid::SECP256K1, 256, 256);
//     pub static ref P384: Curve = Curve::new(Nid::SECP384R1, 384, 384);
//     pub static ref P521: Curve = Curve::new(Nid::SECP521R1, 528, 528);
// }

// pub struct Curve {
//     v: EcGroup,
//     pub order: BigNum,
//     pub fr_bits: usize,
//     pub fr_bytes: usize,
//     pub fq_bits: usize,
//     pub fq_bytes: usize,
// }

// impl Curve {
//     pub fn new(id: Nid, fr_bits: usize, fq_bits: usize) -> Self {
//         let mut order = BigNum::new().unwrap();
//         let v = EcGroup::from_curve_name(id).unwrap();
//         v.order(&mut order, &mut BigNumContext::new().unwrap())
//             .unwrap();
//         Self {
//             v,
//             fr_bits,
//             fr_bytes: (fr_bits + 7) / 8,
//             fq_bits,
//             fq_bytes: (fq_bits + 7) / 8,
//             order,
//         }
//     }

//     pub fn rand_scalar<R: Rng>(&'static self, rng: &mut R) -> Scalar {
//         Scalar { v: k256::Scalar::random(rng) }
//     }

//     pub fn rand_scalar_and_point<R: Rng>(&'static self,rng: &mut R) -> (Scalar, Point) {
//         let mut scalar = self.rand_scalar(rng);
//         let point = Point::from_scalar(self, &scalar);
//         (scalar, point)
//     }

//     pub fn parse_scalar(&'static self, bytes: &[u8]) -> Scalar {
//         Scalar::from_bytes(self, bytes)
//     }

//     pub fn parse_point(&'static self, bytes: &[u8]) -> Point {
//         Point::from_bytes(self, bytes)
//     }

//     pub fn read_scalar<R: Read>(&'static self, reader: &mut R) -> Scalar {
//         Scalar::from_reader(self, reader)
//     }

//     pub fn read_point<R: Read>(&'static self, reader: &mut R) -> Point {
//         Point::from_reader(self, reader)
//     }
// }

// pub struct Point {
//     v: k256::ProjectivePoint,
// }

// impl Point {
//     pub fn from_scalar(curve: &'static Curve, scalar: &Scalar) -> Self {
//         Self {
//             v: k256::ProjectivePoint::GENERATOR * scalar.v
//         }
//     }

//     pub fn from_bytes(curve: &'static Curve, bytes: &[u8]) -> Self {
//         Self {
//             v: k256::ProjectivePoint::from_encoded_point(&k256::EncodedPoint::from_bytes(bytes).unwrap()).unwrap()
//         }
//     }

//     pub fn from_reader<R: Read>(curve: &'static Curve, reader: &mut R) -> Self {
//         let mut bytes = vec![0u8; curve.fq_bytes * 2 + 1];
//         reader.read_exact(&mut bytes).unwrap();
//         Self::from_bytes(curve, &bytes)
//     }

//     pub fn inf(curve: &'static Curve) -> Self {
//         Self {
//             v: k256::ProjectivePoint::IDENTITY
//         }
//     }

//     pub fn gen(curve: &'static Curve) -> Self {
//         Self {
//             v: k256::ProjectivePoint::GENERATOR
//         }
//     }

//     pub fn to_bytes(&self) -> Vec<u8> {
//         self.v.to_encoded_point(false).to_bytes().to_vec()
//     }

//     pub fn add(&self, other: &Self) -> Self {
//         Self {v: self.v + other.v}
//     }

//     pub fn mul(&self, scalar: &Scalar) -> Self {
//         Self {v: self.v * scalar.v}
//     }

//     pub fn neg(&self) -> Self {
//         Self { v: -self.v }
//     }

//     pub fn x_bytes(&self) -> Vec<u8> {
//         self.v.to_affine().x().to_vec()
//     }
// }

// impl PartialEq for Point {
//     fn eq(&self, other: &Self) -> bool {
//         self.v.eq(&other.v)
//     }
// }

// impl Clone for Point {
//     fn clone(&self) -> Self {
//         Self {
//             v: self.v.clone()
//         }
//     }
// }

// impl Debug for Point {
//     fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
//         write!(f, "Point({:?})", self.to_bytes())
//     }
// }

// pub struct Scalar {
//     v: k256::Scalar,
// }

// impl Scalar {
//     pub fn from_bytes(curve: &'static Curve, bytes: &[u8]) -> Self {
//         Self {
//             v: k256::Scalar::from_repr(*GenericArray::from_slice(bytes)).unwrap(),
//         }
//     }

//     pub fn from_reader<R: Read>(curve: &'static Curve, reader: &mut R) -> Self {
//         let mut bytes = vec![0u8; curve.fr_bytes];
//         reader.read_exact(&mut bytes).unwrap();
//         Self::from_bytes(curve, &bytes)
//     }

//     pub fn to_bytes(&self) -> Vec<u8> {
//         self.v.to_repr().to_vec()
//     }

//     pub fn zero(curve: &'static Curve) -> Self {
//         Self {
//             v: k256::Scalar::ZERO,
//         }
//     }

//     pub fn one(curve: &'static Curve) -> Self {
//         Self {
//             v: k256::Scalar::ONE,
//         }
//     }

//     pub fn from_u32(curve: &'static Curve, n: u32) -> Self {
//         Self {
//             v: k256::Scalar::from(n as u64),
//         }
//     }

//     pub fn two_to_n(curve: &'static Curve, n: usize) -> Self {
//         let mut r = k256::U256::ONE;
//         let r = r.shl_vartime(n);
//         Self {
//             v: k256::Scalar::from_uint_reduced(r),
//         }
//     }

//     pub fn add(&self, other: &Self) -> Self {
//         Self {
//             v: self.v.add(&other.v),
//         }
//     }

//     pub fn sub(&self, other: &Self) -> Self {
//         Self {
//             v: self.v.sub(&other.v),
//         }
//     }

//     pub fn mul(&self, other: &Self) -> Self {
//         Self {
//             v: self.v.mul(&other.v),
//         }
//     }

//     pub fn sqr(&self) -> Self {
//         Self { v: self.v.square() }
//     }

//     pub fn neg(&self) -> Self {
//         Self { v: -self.v }
//     }

//     pub fn inv(&self) -> Self {
//         Self {
//             v: self.v.invert().unwrap(),
//         }
//     }
// }

// impl PartialEq for Scalar {
//     fn eq(&self, other: &Self) -> bool {
//         self.v.eq(&other.v)
//     }
// }

// impl Clone for Scalar {
//     fn clone(&self) -> Self {
//         Self { v: self.v.clone() }
//     }
// }

// impl Debug for Scalar {
//     fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
//         write!(f, "Scalar({:?})", self.v.to_repr())
//     }
// }
