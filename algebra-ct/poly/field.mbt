///|
/// # Finite field K = GF(p)
///
/// Everything in the compile-time engine is exact integer arithmetic modulo a
/// prime `p`.  We never use rational numbers, so the emitted runtime code is
/// pure integer arithmetic with no division, no floating point and no
/// normalization pass.
///
/// **Axiom (field).** `K = GF(p)` is a field iff `p` is prime; then
/// every `a != 0` has a multiplicative inverse `a^(p-2)`, computable by
/// Fermat's little theorem (`a^p = a  (mod p)`).
///
/// **Complexity.** `inv` is `O(log p)` modular multiplications by binary
/// exponentiation; the alternative (`a^(p-2)` by repeated squaring) is the
/// same, so the generator uses square-and-multiply, which touches
/// `2*log2(p)` residues.
pub(all) struct Fp {
  p : Int32
}

///|
pub fn Fp::new(p : Int32) -> Fp {
  { p, }
}

///|
/// Additive order of `K^times`, used by Fermat inversion.
pub fn Fp::order(self : Fp) -> Int32 {
  self.p - 1
}

///|
/// Reduce an `Int` into the canonical representative `0..p-1`.
pub fn Fp::norm(self : Fp, a : Int32) -> Int32 {
  let r = a % self.p
  if r < 0 {
    r + self.p
  } else {
    r
  }
}

///|
/// Field addition: `a + b (mod p)`.
pub fn Fp::add(self : Fp, a : Int32, b : Int32) -> Int32 {
  self.norm(a + b)
}

///|
/// Field multiplication: `a * b (mod p)`.
pub fn Fp::mul(self : Fp, a : Int32, b : Int32) -> Int32 {
  self.norm(a * b)
}

///|
/// Field subtraction: `a - b (mod p)`.
pub fn Fp::sub(self : Fp, a : Int32, b : Int32) -> Int32 {
  self.norm(a - b)
}

///|
/// Field negation: `-a (mod p)`.
pub fn Fp::neg(self : Fp, a : Int32) -> Int32 {
  self.norm(-a)
}

///|
/// Multiplicative inverse, by Fermat's little theorem: `a^-1 = a^(p-2)`.
///
/// `a = 0` yields `0` (for `p > 2`): the engine keeps the inner loops branch
/// free, so the zero case is a documented precondition on the caller, not a
/// runtime error.  Every division site in this package guards the divisor
/// with `is_nonzero`/`inv(1)` first, and `span_basis`, `nullspace` and
/// `right_inverse` only ever invert a pivot, which is non-zero by
/// construction.
pub fn Fp::inv(self : Fp, a : Int32) -> Int32 {
  self.pow(self.norm(a), self.p - 2)
}

///|
/// `a^e (mod p)` by square-and-multiply: `O(log e)` multiplications.
pub fn Fp::pow(self : Fp, a : Int32, e : Int32) -> Int32 {
  let mut base = self.norm(a)
  let mut acc = 1
  let mut k = e
  while k > 0 {
    if k % 2 == 1 {
      acc = self.mul(acc, base)
    }
    base = self.mul(base, base)
    k = k / 2
  }
  acc
}

///|
pub fn Fp::is_zero(self : Fp, a : Int32) -> Bool {
  self.norm(a) == 0
}

///|
pub fn Fp::is_nonzero(self : Fp, a : Int32) -> Bool {
  self.norm(a) != 0
}

///|
/// Primality test by trial division up to `sqrt(p)`; used once, at build time,
/// to validate the field modulus coming from the specification.
pub fn is_prime(p : Int32) -> Bool {
  if p < 2 {
    return false
  }
  if p == 2 {
    return true
  }
  if p % 2 == 0 {
    // even and > 2, hence composite; the odd-only loop below would have
    // skipped the divisor 2 entirely and answered `true`.
    return false
  }
  // `p` odd from here on, so only the odd divisors have to be tried.
  let mut d = 3
  let mut ok = true
  while ok && d * d <= p {
    if p % d == 0 {
      ok = false
    }
    d += 2
  }
  ok
}

///|
/// `K^times` is cyclic of order `p-1`; an element `g` is a generator iff
/// `g^((p-1)/q) != 1` for every prime divisor `q` of `p-1`.
pub fn Fp::is_primitive(self : Fp, g : Int32) -> Bool {
  let n = self.order()
  let mut m = n
  let mut d = 2
  let mut ok = true
  while ok && d * d <= m {
    if m % d == 0 {
      if self.pow(g, n / d) == 1 {
        ok = false
      }
      while m % d == 0 {
        m = m / d
      }
    }
    d += 1
  }
  // Whatever survives the trial division is either 1 (fully factored) or a
  // single prime divisor `q` of `n`; in the latter case the test is still
  // `g^(n/q) != 1` -- *not* `g^q != 1`, which accepts elements of order `q`.
  if ok && m > 1 && self.pow(g, n / m) == 1 {
    ok = false
  }
  ok
}
