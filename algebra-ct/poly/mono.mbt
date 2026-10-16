///|
/// # Monomials of a polynomial ring `K[x_1, ..., x_n]`
///
/// **Definition.** For `n >= 0` the free commutative monoid on
/// `x_1, ..., x_n` is `N^n`; writing `m = m_1 x_1^(e_1) * ... * x_n^(e_n)`
/// we identify a monomial with its exponent vector `e = (e_1, ..., e_n)`.
///
/// The addition is `m + m' = m * m'` (coordinate-wise addition of exponents)
/// and the order unit is `1 = x_1^0 * ... * x_n^0`.  Hence `N^n` is a
/// cancellative, free, well-ordered monoid and every element has a unique
/// factorisation.  This unique factorisation is exactly what lets us store a
/// polynomial as a finite map `monomial -> K` with no further invariant.
///
/// **Representation.** `Array[Int]` of length `n`.  We always *copy* before
/// mutating, because MoonBit arrays are reference-typed and monomials flow
/// through every routine in the engine.
pub fn mono_zero(n : Int32) -> Array[Int32] {
  Array::make(n, 0)
}

///|
/// The order unit `1 = x_1^0 ... x_n^0`.
pub fn mono_one(n : Int32) -> Array[Int32] {
  Array::make(n, 0)
}

///|
/// The `i`-th variable `x_i` (0-based).
pub fn mono_var(n : Int32, i : Int32) -> Array[Int32] {
  let m = Array::make(n, 0)
  m[i] = 1
  m
}

///|
/// Canonical, injective string key of an exponent vector.  Used as the hash
/// key of the sparse coefficient map, so it must be a bijection on `N^n`;
/// the comma separated decimal form is, because decimal digits are canonical.
pub fn mono_key(m : Array[Int32]) -> String {
  let buf = StringBuilder()
  let mut i = 0
  while i < m.length() {
    if i > 0 {
      buf.write_char(',')
    }
    buf.write_string(m[i].to_string())
    i = i + 1
  }
  buf.to_string()
}

///|
/// Inverse of `mono_key`.
pub fn mono_parse(s : String) -> Array[Int32] {
  s
  .split(",")
  .map(x => {
    let v = @string.parse_int(x) catch { _ => 0 }
    v
  })
  .to_array()
}

///|
/// Monomial addition `m + m' = m * m'`.
pub fn mono_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  let mut i = 0
  while i < a.length() {
    out[i] = a[i] + b[i]
    i = i + 1
  }
  out
}

///|
/// Monomial quotient, when it exists (`b | a`).
pub fn mono_div(a : Array[Int32], b : Array[Int32]) -> Array[Int32]? {
  let out = Array::make(a.length(), 0)
  let mut i = 0
  while i < a.length() {
    if b[i] > a[i] {
      return None
    }
    out[i] = a[i] - b[i]
    i = i + 1
  }
  Some(out)
}

///|
/// LCM in the monoid: `max(a_i, b_i)`.
pub fn mono_lcm(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  let mut i = 0
  while i < a.length() {
    out[i] = if a[i] >= b[i] { a[i] } else { b[i] }
    i = i + 1
  }
  out
}

///|
/// Greatest common divisor, componentwise minimum.
pub fn mono_gcd(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  let mut i = 0
  while i < a.length() {
    out[i] = if a[i] <= b[i] { a[i] } else { b[i] }
    i += 1
  }
  out
}

///|
/// `a / b` when `b` divides `a`, all-zero otherwise.  (The argument order
/// mirrors `mono_div_by`, which answers "does the second argument divide the
/// first".)
pub fn mono_div_safe(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  let mut i = 0
  while i < a.length() {
    if b[i] > a[i] {
      return mono_zero(a.length())
    }
    out[i] = a[i] - b[i]
    i += 1
  }
  out
}

///|
/// `true` iff `b` divides `a`.
pub fn mono_multiple_of(a : Array[Int32], b : Array[Int32]) -> Bool {
  mono_div_by(b, a)
}

///|
/// `b` divides `a`.
///
/// `true` iff `b` divides `a`, i.e. `a = b * c` for a monomial `c` -- **note
/// the order**: the *multiple* comes first.  An earlier version of this
/// function was called `mono_div_by(a, b)`, which reads as the opposite, and
/// two call sites did get it backwards (a Gröbner basis of the unit ideal came
/// out empty because `x^3` was believed to divide `1`).
pub fn mono_div_by(a : Array[Int32], b : Array[Int32]) -> Bool {
  let mut i = 0
  while i < a.length() {
    if b[i] > a[i] {
      return false
    }
    i += 1
  }
  true
}

///|
/// `m == m'`.
pub fn mono_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  mono_key(a) == mono_key(b)
}

///|
/// Total degree `|m| = e_1 + ... + e_n`.  A monomial order must satisfy
/// `|m| <= |m * m'|`, so degree is an order-refining map.
pub fn mono_total_degree(m : Array[Int32]) -> Int32 {
  let mut s = 0
  let mut i = 0
  while i < m.length() {
    s += m[i]
    i = i + 1
  }
  s
}

///|
/// A human readable monomial, e.g. `x0^2*x2`.
pub fn mono_show(m : Array[Int32]) -> String {
  let parts : Array[String] = []
  let mut i = 0
  while i < m.length() {
    if m[i] > 0 {
      parts.push(if m[i] == 1 { "x\{i}" } else { "x\{i}^\{m[i]}" })
    }
    i = i + 1
  }
  match parts.length() {
    0 => "1"
    _ => parts.join("*")
  }
}
