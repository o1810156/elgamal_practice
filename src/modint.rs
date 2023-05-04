use num_traits::{
    identities::{One, Zero},
    Num,
};
use std::fmt;
use std::ops;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ModInt {
    val: u64,
    mod_: u64,
}

impl Num for ModInt {
    type FromStrRadixErr = <usize as Num>::FromStrRadixErr;

    fn from_str_radix(_str: &str, _radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        panic!("ModInt::from_str_radix is not implemented");
    }
}

impl fmt::Display for ModInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl ModInt {
    pub fn new(n: u64, mod_: u64) -> Self {
        Self {
            val: n % mod_,
            mod_,
        }
    }

    pub fn val(&self) -> u64 {
        // 念のためMOD演算
        self.val % self.mod_
    }

    pub fn _set_val(&mut self, val: u64) {
        self.val = val % self.mod_;
    }

    pub fn pow(&self, mut n: u64) -> Self {
        let mut val = self.val;
        let mod_ = self.mod_;
        let mut res: u64 = 1;
        while n > 0 {
            if n % 2 == 1 {
                res = ((res as u128 * val as u128) % mod_ as u128) as u64;
            }
            val = ((val as u128 * val as u128) % mod_ as u128) as u64;
            n /= 2;
        }

        Self { val: res, mod_ }
    }

    /*
    pub fn pow(&self, other: Self) -> Self {
        if self.mod_ != other.mod_ {
            panic!("ModInt.pow: different mod");
        }

        self.pow_u(other.val)
    }
    */

    pub fn inv(&self) -> Self {
        self.pow(self.mod_ - 2)
    }

    fn added_val(self, other: Self) -> u64 {
        ((self.val as u128 + other.val as u128) % self.mod_ as u128) as u64
    }

    fn muled_val(self, other: Self) -> u64 {
        ((self.val as u128 * other.val as u128) % self.mod_ as u128) as u64
    }

    fn subed_val(self, other: Self) -> u64 {
        ((self.val as i128 - other.val as i128 + self.mod_ as i128) % self.mod_ as i128) as u64
    }
}

impl ops::Add for ModInt {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        if self.mod_ != other.mod_ {
            panic!("ModInt.add: different mod");
        }

        Self {
            val: self.added_val(other),
            mod_: self.mod_,
        }
    }
}

impl ops::AddAssign for ModInt {
    fn add_assign(&mut self, other: Self) {
        if self.mod_ != other.mod_ {
            panic!("ModInt.add_assign: different mod");
        }

        *self = Self {
            val: self.added_val(other),
            mod_: self.mod_,
        };
    }
}

impl ops::Mul for ModInt {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        if self.mod_ != other.mod_ {
            panic!("ModInt.mul: different mod");
        }

        Self {
            val: self.muled_val(other),
            mod_: self.mod_,
        }
    }
}

impl ops::MulAssign for ModInt {
    fn mul_assign(&mut self, other: Self) {
        if self.mod_ != other.mod_ {
            panic!("ModInt.mul_assign: different mod");
        }

        *self = Self {
            val: self.muled_val(other),
            mod_: self.mod_,
        };
    }
}

impl ops::Sub for ModInt {
    type Output = Self;

    fn sub(mut self, other: Self) -> Self {
        if self.mod_ != other.mod_ {
            panic!("ModInt.sub: different mod");
        }

        if self.val < other.val {
            self.val += self.mod_;
        }

        Self {
            val: self.subed_val(other),
            mod_: self.mod_,
        }
    }
}

impl ops::SubAssign for ModInt {
    fn sub_assign(&mut self, other: Self) {
        if self.mod_ != other.mod_ {
            panic!("ModInt.sub_assign: different mod");
        }

        if self.val < other.val {
            self.val += self.mod_;
        }

        *self = Self {
            val: self.subed_val(other),
            mod_: self.mod_,
        };
    }
}

impl ops::Div for ModInt {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        if self.mod_ != other.mod_ {
            panic!("ModInt.div: different mod");
        }

        if other.val == 0 {
            panic!("0 division occured.");
        }

        self * other.inv()
    }
}

impl ops::DivAssign for ModInt {
    fn div_assign(&mut self, other: Self) {
        if self.mod_ != other.mod_ {
            panic!("ModInt.div_assign: different mod");
        }

        if other.val == 0 {
            panic!("0 division occured.");
        }

        *self *= other.inv();
    }
}

impl ops::Rem for ModInt {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        if self.mod_ != other.mod_ {
            panic!("ModInt.rem: different mod");
        }

        Self {
            val: (self.val % other.val) % self.mod_, // 念のためMOD演算
            mod_: self.mod_,
        }
    }
}

impl ops::RemAssign for ModInt {
    fn rem_assign(&mut self, other: Self) {
        if self.mod_ != other.mod_ {
            panic!("ModInt.rem_assign: different mod");
        }

        *self = Self {
            val: (self.val % other.val) % self.mod_, // 念のためMOD演算
            mod_: self.mod_,
        };
    }
}

impl Zero for ModInt {
    fn zero() -> Self {
        panic!("ModInt.zero: zero is not defined.");
    }

    fn is_zero(&self) -> bool {
        self.val == 0
    }

    fn set_zero(&mut self) {
        self.val = 0;
    }
}

impl One for ModInt {
    fn one() -> Self {
        panic!("ModInt.one: one is not defined.");
    }

    fn is_one(&self) -> bool {
        self.val == 1
    }

    fn set_one(&mut self) {
        self.val = 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MOD: u64 = 1_000_000_007;

    #[test]
    fn test1() {
        let a = ModInt::new(111, MOD);
        let b = ModInt::new(222, MOD);
        let c = ModInt::new(333, MOD);
        let d = ModInt::new(444, MOD);

        let res = a * b + c - d;
        assert_eq!(res.val(), 24531);
    }

    #[test]
    fn test2() {
        let a = ModInt::new(111111111, MOD);
        let b = ModInt::new(222222222, MOD);
        let c = ModInt::new(333333333, MOD);
        let d = ModInt::new(444444444, MOD);

        let res = a * b + c - d;
        assert_eq!(res.val(), 691358032);
    }
}
