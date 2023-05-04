use crate::modint::ModInt;
use crate::prime::{miller_rabin, primitive_root};
use rand::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct PubKey {
    p: u64,
    g: ModInt,
    z: ModInt,
}

impl PubKey {
    pub fn get_p(&self) -> u64 {
        self.p
    }
}

#[derive(Debug)]
pub struct SecKey {
    x: ModInt,
}

pub fn keygen<R>(p: u64, rng: &mut R) -> (PubKey, SecKey)
where
    R: Rng + CryptoRng,
{
    let g = primitive_root(p, rng);
    let g = ModInt::new(g, p);
    let x = ModInt::new(rng.gen_range(0..p - 1), p);
    let z = g.pow(x.val());
    let pk = PubKey { p, g, z };
    let sk = SecKey { x };
    (pk, sk)
}

pub fn keygen_for_u8<R>(rng: &mut R) -> (PubKey, SecKey)
where
    R: Rng + CryptoRng,
{
    let p = loop {
        let p = rng.gen_range((u32::MAX as u64 + 1)..u64::MAX);
        if miller_rabin(p) {
            break p;
        }
    };
    keygen(p, rng)
}

#[derive(Debug, Clone, Copy)]
pub struct Ciphertext {
    c0: ModInt,
    c1: ModInt,
}

impl fmt::Display for Ciphertext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(c0: {}, c1: {})", self.c0, self.c1)
    }
}

use std::ops;

impl ops::Mul for Ciphertext {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self {
            c0: self.c0 * other.c0,
            c1: self.c1 * other.c1,
        }
    }
}

impl ops::MulAssign for Ciphertext {
    fn mul_assign(&mut self, other: Self) {
        *self = Self {
            c0: self.c0 * other.c0,
            c1: self.c1 * other.c1,
        };
    }
}

pub fn display_cipvec(v: &Vec<Ciphertext>) -> String {
    let mut s = String::from("[");
    for c in v {
        s.push_str(&format!("{}, ", c));
    }
    s.push_str("]");
    s
}

impl PubKey {
    pub fn encrypt<R>(&self, m: u64, rng: &mut R) -> Result<Ciphertext, ()>
    where
        R: Rng + CryptoRng,
    {
        if m >= self.p {
            return Err(());
        }

        let r = ModInt::new(rng.gen_range(2..self.p), self.p);
        let c0 = self.z.pow(r.val()) * ModInt::new(m, self.p);
        let c1 = self.g.pow(r.val());
        Ok(Ciphertext { c0, c1 })
    }

    pub fn enc_vec<R>(&self, v: &[u8], rng: &mut R) -> Result<Vec<Ciphertext>, ()>
    where
        R: Rng + CryptoRng,
    {
        v.iter().map(|&m8| self.encrypt(m8 as u64, rng)).collect()
    }

    pub fn enc_str<R>(&self, s: &str, rng: &mut R) -> Result<Vec<Ciphertext>, ()>
    where
        R: Rng + CryptoRng,
    {
        self.enc_vec(s.as_bytes(), rng)
    }
}

impl SecKey {
    pub fn decrypt(&self, c: &Ciphertext) -> u64 {
        let inv = c.c1.pow(self.x.val()).inv();
        (c.c0 * inv).val()
    }

    pub fn dec_vec(&self, v: &[Ciphertext]) -> Vec<u8> {
        v.iter().map(|c| self.decrypt(c) as u8).collect()
    }

    pub fn dec_str(&self, v: &[Ciphertext]) -> Result<String, std::string::FromUtf8Error> {
        String::from_utf8(self.dec_vec(v))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_u64() {
        use super::*;
        use rand::rngs::StdRng;
        use rand::SeedableRng;
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, sk) = keygen_for_u8(&mut rng);
        let v = pk.encrypt(42, &mut rng).unwrap();
        let m = sk.decrypt(&v);
        assert_eq!(m, 42);
    }

    #[test]
    fn test_vec() {
        use super::*;
        use rand::rngs::StdRng;
        use rand::SeedableRng;
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, sk) = keygen_for_u8(&mut rng);
        let v = pk.enc_vec(b"Hello, world!", &mut rng).unwrap();
        let s = sk.dec_vec(&v);
        assert_eq!(s, b"Hello, world!");
    }

    #[test]
    fn test_str() {
        use super::*;
        use rand::rngs::StdRng;
        use rand::SeedableRng;
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, sk) = keygen_for_u8(&mut rng);
        let v = pk.enc_str("Hello, world!", &mut rng).unwrap();
        let s = sk.dec_str(&v).unwrap();
        assert_eq!(s, "Hello, world!");
    }

    #[test]
    fn chacha_test() {
        use super::*;
        use rand_chacha::ChaChaRng;
        let mut rng = ChaChaRng::from_entropy();
        let (pk, sk) = keygen_for_u8(&mut rng);
        let v = pk.enc_str("Hello, world!", &mut rng).unwrap();
        let s = sk.dec_str(&v).unwrap();
        assert_eq!(s, "Hello, world!");
    }
}
