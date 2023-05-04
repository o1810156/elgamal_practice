use std::collections::HashSet;
use rand::prelude::*;

// https://zenn.dev/kaki_xxx/articles/40a92b43200215

fn modpow(base: u64, mut exp: u64, m: u64) -> u64 {
    let mut ret = 1;
    let mut pow = base;
    while exp != 0 {
        if exp & 1 != 0 {
            ret = ((ret as u128 * pow as u128) % m as u128) as u64;
        }
        pow = ((pow as u128 * pow as u128) % m as u128) as u64;
        exp >>= 1;
    }
    ret
}

pub fn miller_rabin(n: u64) -> bool {
    if n <= 2 {
        return n == 2
    }
    if n % 2 == 0 {
        return false;
    }

    // 2^s の s
    let mut s = 0;
    let mut t = n-1;
    while t % 2 == 0 {
        s += 1;
        t /= 2;
    }
    // n - 1 == 2^s * t

    let is_prime = |a| {
        let mut x = modpow(a, t, n);
        if x == 1 || x == n-1 {
            return true;
        }
        for _ in 0..s-1 {
            x = ((x as u128 * x as u128) % n as u128) as u64;
            if x == n-1 {
                return true;
            }
        }
        false
    };
    for &a in &[2, 325, 9375, 28178, 450775, 9780504, 1795265022] {
        let mut a = a;

        if a >= n {
            a = a % n;
            if a == 0 {
                return true;
            }
        }

        if !is_prime(a) {
            return false;
        }
    }
    true 
}

// https://seasawher.hatenablog.com/entry/2022/05/11/010000
// https://manabitimes.jp/math/1192

fn gcd(a: u64, b: u64) -> u64 {
    let x = a.max(b);
    let y = a.min(b);

    if y == 0 {
        x
    } else {
        gcd(y, x % y)
    }
}

fn rho<R: Rng>(n: u64, rng: &mut R) -> Option<u64> {
    if n <= 20 {
        for i in 2..n {
            if n % i == 0 {
                return Some(i);
            }
        }
        return None;
    }

    let f = |x| {
        let x = x % n;
        let x = ((x as u128 * x as u128) % n as u128) as u64;
        (x + 1) % n
    };

    let mut x: u64 = rng.gen_range(2..n);
    let mut y = f(x);

    loop {
        let diff = (y as i128 - x as i128).abs() as u64;
        let d = gcd(diff, n);

        if d == 1 {
            x = f(x);
            y = f(f(y));
            continue;
        } else if 1 < d && d < n {
            return Some(d);
        } else { // n == d
            return None;
        }
    }
}

fn rho_rec<R: Rng>(n: u64, rng: &mut R, ret: &mut HashSet<u64>) {
    if n == 1 {
        return;
    }
    if miller_rabin(n) {
        ret.insert(n);
        return;
    }
    for _ in 0..10 {
        if let Some(d) = rho(n, rng) {
            rho_rec(d, rng, ret);
            rho_rec(n / d, rng, ret);
            break;
        } /* else {
            ret.insert(n);
        } */
    }
}

pub fn prime_fact_cands<R: Rng>(n: u64, rng: &mut R) -> Vec<(u64, u32)> {
    let mut ret = HashSet::new();
    let nn = n;

    rho_rec(nn, rng, &mut ret);

    let mut ret = ret.into_iter().collect::<Vec<_>>();
    ret.sort();

    ret.into_iter().map(|m| {
        let mut i = 0;
        let mut nn = n;
        while nn % m == 0 {
            i += 1;
            nn /= m;
        }

        (m, i)
    }).collect()
}

pub fn prime_fact<R: Rng>(n: u64, rng: &mut R) -> Option<Vec<(u64, u32)>> {
    let mut res = None;
    for _ in 0..10000 {
        let cands = prime_fact_cands(n, rng);
        if cands.iter().map(|(p, i)| p.pow(*i)).product::<u64>() == n {
            res = Some(cands);
            break;
        }
    }
    res
}

pub fn primitive_root<R: Rng>(prime: u64, rng: &mut R) -> u64 {
    let factors = prime_fact(prime - 1, rng).unwrap();

    let mut res = 1;

    for (q, e) in factors {
        let mut a = 0;
        let mut b = 0;
        for _ in 0_u64..10000000000 {
            a = rng.gen_range(2..prime);
            b = modpow(a, (prime - 1) / q, prime);
            if b != 1 {
                break;
            }
        }

        if b == 1 {
            panic!("not found");
        }

        res = ((res as u128 * modpow(a, (prime - 1) / (q.pow(e)), prime) as u128) % prime as u128) as u64;
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test1() {
        assert!(miller_rabin(2));
        assert!(miller_rabin(3));
        assert!(miller_rabin(5));
        assert!(miller_rabin(7));
        assert!(miller_rabin(11));
        assert!(miller_rabin(13));
        assert!(miller_rabin(17));
        assert!(miller_rabin(19));
        assert!(miller_rabin(23));
        assert!(miller_rabin(29));
        assert!(miller_rabin(31));
        assert!(miller_rabin(37));
    }

    fn naive_prime_gen(m: u64) -> Vec<u64> {
        let mut primes = vec![2];
        for i in 3..m {
            if primes.iter().all(|&p| i % p != 0) {
                primes.push(i);
            }
        }

        primes
    }

    #[test]
    fn test2() {
        let primes = naive_prime_gen(100000);
        for &p in &primes {
            assert!(miller_rabin(p));
        }
    }

    fn prfc_sub<R: Rng>(n: u64, rng: &mut R) {
        if miller_rabin(n) {
            return;
        }

        let pf = prime_fact(n, rng).unwrap();
        // println!("{:?}", pf);
        assert_eq!(pf.iter().map(|(p, i)| p.pow(*i)).product::<u64>(), n);
    }

    #[test]
    fn prime_fact_test() {
        let mut rng = rand::thread_rng();

        prfc_sub(31415926535, &mut rng);

        for _ in 0..10000 {
            let n = rng.gen();

            prfc_sub(n, &mut rng);
        }
    }

    fn prime_gen(m: u64) -> Vec<u64> {
        let mut primes = vec![2];
        for i in 3..m {
            if miller_rabin(i) {
                primes.push(i);
            }
        }

        primes
    }

    #[test]
    fn primitive_root_test() {
        let mut rng = rand::thread_rng();

        let primes = prime_gen(10000);
        for &p in &primes {
            let g = primitive_root(p, &mut rng);
            let mut i = 1;
            while modpow(g, i, p) != 1 {
                i += 1;
            }
            // println!("{} {} {}", g, p, i);
            assert_eq!(i, p - 1);
        }

        println!("beep");

        // for big prime
        // と思ったけど調べる手段が離散対数問題
    }
}