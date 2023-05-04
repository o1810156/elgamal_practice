use crate::modint::ModInt;
use crate::prime::{miller_rabin, primitive_root};
use rand::prelude::*;
use std::fmt;

#[derive(Debug, Clone)]
pub struct PubKey {
    q: u64,
    hk: u64,
    g: ModInt,
    g_hat: ModInt,
    e: ModInt,
    f: ModInt,
    h: ModInt,
}

impl PubKey {
    fn hash(&self, a: ModInt, a_hat: ModInt, c: ModInt) -> ModInt {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&self.hk.to_be_bytes());
        hasher.update(&a.val().to_be_bytes());
        hasher.update(&a_hat.val().to_be_bytes());
        hasher.update(&c.val().to_be_bytes());
        let h = hasher.finalize();
        let hash_vec = h.as_bytes();

        let mut res = ModInt::new(1, self.q);

        for &m in hash_vec {
            res *= ModInt::new(m as u64, self.q);
        }

        res
    }
}

#[derive(Debug)]
pub struct SecKey {
    pk: PubKey,
    x1: ModInt,
    x2: ModInt,
    y1: ModInt,
    y2: ModInt,
    z1: ModInt,
    z2: ModInt,
}

pub fn keygen<R>(q: u64, rng: &mut R) -> (PubKey, SecKey)
where
    R: Rng + CryptoRng,
{
    let hk: u64 = rng.gen();

    let g = primitive_root(q, rng);
    let g = ModInt::new(g, q);
    let w = ModInt::new(rng.gen_range(0..q - 1), q);
    let g_hat = g.pow(w.val());

    let x1 = ModInt::new(rng.gen_range(0..q - 1), q);
    let x2 = ModInt::new(rng.gen_range(0..q - 1), q);
    let e = g.pow(x1.val()) * g_hat.pow(x2.val());

    let y1 = ModInt::new(rng.gen_range(0..q - 1), q);
    let y2 = ModInt::new(rng.gen_range(0..q - 1), q);
    let f = g.pow(y1.val()) * g_hat.pow(y2.val());

    let z1 = ModInt::new(rng.gen_range(0..q - 1), q);
    let z2 = ModInt::new(rng.gen_range(0..q - 1), q);
    let h = g.pow(z1.val()) * g_hat.pow(z2.val());

    let pk = PubKey {
        q,
        hk,
        g,
        g_hat,
        e,
        f,
        h,
    };
    let sk = SecKey {
        pk: pk.clone(),
        x1,
        x2,
        y1,
        y2,
        z1,
        z2,
    };
    (pk, sk)
}

pub fn keygen_for_u8<R>(rng: &mut R) -> (PubKey, SecKey)
where
    R: Rng + CryptoRng,
{
    let q = loop {
        let q = rng.gen_range((u32::MAX as u64 + 1)..u64::MAX);
        if miller_rabin(q) {
            break q;
        }
    };
    keygen(q, rng)
}

#[derive(Debug, Clone, Copy)]
pub struct Ciphertext {
    a: ModInt,
    a_hat: ModInt,
    c: ModInt,
    d: ModInt,
}

impl fmt::Display for Ciphertext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(a: {}, a_hat: {}, c: {}, d: {})",
            self.a, self.a_hat, self.c, self.d
        )
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
        if m >= self.q {
            return Err(());
        }

        // e1
        let u = ModInt::new(rng.gen_range(0..self.q - 1), self.q).val();

        // e2
        let a = self.g.pow(u);

        // e3
        let a_hat = self.g_hat.pow(u);

        // e4
        let c = self.h.pow(u) * ModInt::new(m, self.q);

        // e5
        let v = self.hash(a, a_hat, c);

        // e6
        let d = self.e.pow(u) * self.f.pow(u).pow(v.val());

        // e7
        Ok(Ciphertext { a, a_hat, c, d })
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
    pub fn decrypt(&self, c: &Ciphertext) -> Option<u64> {
        // d3
        let v_dash = self.pk.hash(c.a, c.a_hat, c.c);

        // d4
        let d = c.a.pow(self.x1.val())
            * c.a.pow(self.y1.val()).pow(v_dash.val())
            * c.a_hat.pow(self.x2.val())
            * c.a_hat.pow(self.y2.val()).pow(v_dash.val());

        if d != c.d {
            return None;
        }

        // d5
        let m_dash = c.c * (c.a.pow(self.z1.val()) * c.a_hat.pow(self.z2.val())).inv();

        Some(m_dash.val())
    }

    pub fn dec_vec(&self, v: &[Ciphertext]) -> Option<Vec<u8>> {
        v.iter().map(|c| self.decrypt(c).map(|m| m as u8)).collect()
    }

    pub fn dec_str(&self, v: &[Ciphertext]) -> Result<Option<String>, std::string::FromUtf8Error> {
        self.dec_vec(v).map(|m| String::from_utf8(m)).transpose()
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
        let m = sk.decrypt(&v).unwrap();
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
        let s = sk.dec_vec(&v).unwrap();
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
        let s = sk.dec_str(&v).unwrap().unwrap();
        assert_eq!(s, "Hello, world!");
    }

    #[test]
    fn chacha_test() {
        use super::*;
        use rand_chacha::ChaChaRng;
        let mut rng = ChaChaRng::from_entropy();
        let (pk, sk) = keygen_for_u8(&mut rng);
        let v = pk.enc_str("Hello, world!", &mut rng).unwrap();
        let s = sk.dec_str(&v).unwrap().unwrap();
        assert_eq!(s, "Hello, world!");
    }
}
