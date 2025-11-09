// I might want to reimplement ilog for the BigUint type...

// bnum's implementation:

// #[inline]
// const fn iilog(m: ExpType, b: Self, k: Self) -> (ExpType, Self) {
//     // https://people.csail.mit.edu/jaffer/III/iilog.pdf
//     if b.gt(&k) {
//         (m, k)
//     } else {
//         let (new, q) = Self::iilog(m << 1, b.mul(b), k.div_rem_unchecked(b).0);
//         if b.gt(&q) {
//             (new, q)
//         } else {
//             (new + m, q.div(b))
//         }
//     }
// }

// #[doc = doc::checked::checked_ilog10!(U)]
// #[must_use = doc::must_use_op!()]
// #[inline]
// pub const fn checked_ilog10(self) -> Option<ExpType> {
//     if self.is_zero() {
//         return None;
//     }
//     if Self::TEN.gt(&self) {
//         return Some(0);
//     }
//     Some(Self::iilog(1, Self::TEN, self.div_rem_digit(10).0).0)
// }
// pub(crate) const fn div_rem_digit(self, rhs: $Digit) -> (Self, $Digit) {
//     let mut out = Self::ZERO;
//     let mut rem: $Digit = 0;
//     let mut i = N;
//     while i > 0 {
//         i -= 1;
//         let (q, r) = digit::$Digit::div_rem_wide(self.digits[i], rem, rhs);
//         rem = r;
//         out.digits[i] = q;
//     }
//     (out, rem)
// }
// #[inline]
// pub const fn div_rem_wide(low: Digit, high: Digit, rhs: Digit) -> (Digit, Digit) {
//     debug_assert!(high < rhs);

//     let a = to_double_digit(low, high);
//     (
//         (a / rhs as DoubleDigit) as Digit,
//         (a % rhs as DoubleDigit) as Digit,
//     )
// }
// #[inline]
// pub const fn to_double_digit(low: Digit, high: Digit) -> DoubleDigit {
//     ((high as DoubleDigit) << BITS) | low as DoubleDigit
// }

// fn big_10() -> &'static BigUint {
//     static BIG10: OnceLock<BigUint> = OnceLock::new();
//     BIG10.get_or_init(|| BigUint::from(10u32))
// }


// fn fmt_bigint(n: &BigUint, f: &mut fmt::Formatter) -> fmt::Result {
//     const N_LEADING_DIGITS: u32 = 5;
//     const N_TRAILING_DIGITS: u32 = 5;
//     fn trailing_pow10() -> &'static BigUint {
//         static TRAILING_POW10: OnceLock<BigUint> = OnceLock::new();
//         TRAILING_POW10.get_or_init(|| BigUint::from(10u32.pow(N_TRAILING_DIGITS)))
//     }
    
//     todo!()
// }
