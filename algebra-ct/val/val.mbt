///|
type Fp = @poly.Fp

///|
type IntArray = Array[Int32]

///|
/// # Truncated power series over `K[[t]]` (落特環 / t-進賦值)
///
/// A series is stored as its coefficients `a_0, a_1, ..., a_{N-1}`, i.e. the
/// class of `sum a_i t^i` modulo `t^N`.  This is the ring
/// ```
///   K[[t]] / (t^N)   ~=   K[t] / (t^N)
/// ```
/// which is the Artinian local ring with maximal ideal `(t)` and
/// `dim_k m/m^2 = 1`: it is the DVR `K[[t]]` truncated, the model for every
/// local ring that arises in the system (and the `落特環` of the classical
/// theory: complete, non-discrete-looking, valuation-gluing).
///
/// **Truncation.**  `(a + b) mod t^N` and `a * b mod t^N` are exact because
/// `(t^i)(t^j) = t^{i+j}` and every term of degree `>= N` is killed.
pub type Series = IntArray

///|
/// The `i`-th coefficient, `0` beyond the stored precision.
pub fn coef(s : Series, i : Int32) -> Int32 {
  if i < s.length() {
    s[i]
  } else {
    0
  }
}

///|
/// Truncation of a series to `N` coefficients.
pub fn trunc(s : Series, n : Int32) -> Series {
  let m = if n < s.length() { n } else { s.length() }
  let out = Array::make(n, 0)
  let mut i = 0
  while i < m {
    out[i] = s[i]
    i += 1
  }
  out
}

///|
/// `t`-adic valuation: the least `i` with `a_i != 0`, `+infinity` for `0`.
///
/// **Theorem.**  `v(f g) = v(f) + v(g)` and `v(f + g) >= min(v(f), v(g))`.
/// The truncated ring satisfies the first identity exactly and the second one
/// up to the truncation precision.
pub fn valuation(s : Series) -> Int32 {
  let mut i = 0
  while i < s.length() {
    if s[i] != 0 {
      return i
    }
    i += 1
  }
  -1
}

///|
/// Truncated multiplication, `O(N^2)` field operations.
pub fn series_mul(k : Fp, a : Series, b : Series, n : Int32) -> Series {
  let out = Array::make(n, 0)
  let mut i = 0
  while i < n {
    if coef(a, i) != 0 {
      let mut j = 0
      while i + j < n {
        let bv = coef(b, j)
        if bv != 0 {
          out[i + j] = k.add(out[i + j], k.mul(coef(a, i), bv))
        }
        j += 1
      }
    }
    i += 1
  }
  out
}

///|
/// Newton inversion by precision doubling.
///
/// **Theorem (Newton).**  If `a b = 1 mod t^k` then
/// ```
///   a * b' = 1 - (1 - a b)^2 = 1 mod t^{2k},
/// ```
/// so `b <- b (2 - a b)` doubles the number of correct coefficients each
/// step.  Starting from `b = a_0^{-1}` the loop performs
/// `ceil(log2 N)` iterations instead of the `N` of the naive recurrence,
/// i.e. `O(M(N) log N)` against `O(N M(N))` for `M` the truncated product.
pub fn series_inv(k : Fp, a : Series, n : Int32) -> Series {
  if n == 0 {
    return []
  }
  if coef(a, 0) == 0 {
    return Array::make(n, 0)
  }
  let mut b : Series = [k.inv(coef(a, 0))]
  let mut prec = 1
  while prec < n {
    let two_k = if 2 * prec < n { 2 * prec } else { n }
    let ab = trunc(series_mul(k, a, b, two_k), two_k)
    // c = 2 - a*b   (mod t^{2k})
    let c = Array::make(two_k, 0)
    c[0] = k.norm(2 - ab[0])
    let mut i = 1
    while i < two_k {
      c[i] = k.norm(0 - ab[i])
      i += 1
    }
    b = trunc(series_mul(k, b, c, two_k), two_k)
    prec = two_k
  }
  b
}

///|
/// Truncated square root by the same doubling scheme.
///
/// **Theorem.**  With `b^2 = a mod t^k`, the update `b' = (b + a/b)/2`
/// satisfies `b'^2 = a mod t^{2k}`: writing `b' = b + e`,
/// `b'^2 - a = 2be + e^2` and `e in t^k` because `a/b - b in t^k`.
///
/// `p = 2` is rejected (the update is not defined there) and a non-square
/// constant term yields the zero series, both signalled by an all-zero
/// result.
pub fn series_sqrt(k : Fp, a : Series, n : Int32) -> Series {
  if n == 0 {
    return []
  }
  if coef(a, 0) == 0 {
    return Array::make(n, 0)
  }
  // constant term: b_0 = a_0^{(p+1)/4} works in characteristic 2 or p = 3 mod 4
  // only for a fixed generator, so solve b_0^2 = a_0 by exhaustive search --
  // p is a small compile-time prime, and the search is done once.
  // The Newton update `b <- (b + a/b)/2` divides by `2`, which does not
  // exist in characteristic 2; `series_sqrt` is defined only for odd `p`.
  if k.p == 2 {
    return Array::make(n, 0)
  }
  let target = coef(a, 0)
  let mut b0 = -1
  let mut c = 0
  while c < k.p {
    if k.mul(c, c) == target {
      b0 = c
    }
    c += 1
  }
  if b0 < 0 {
    return Array::make(n, 0)
  }
  let mut b : Series = [b0]
  let mut prec = 1
  while prec < n {
    let two_k = if 2 * prec < n { 2 * prec } else { n }
    let ab = trunc(series_mul(k, a, series_inv(k, b, two_k), two_k), two_k)
    let nb = Array::make(two_k, 0)
    let mut i = 0
    while i < two_k {
      nb[i] = k.add(coef(b, i), ab[i])
      i += 1
    }
    let half = k.inv(k.norm(2))
    let mut i2 = 0
    while i2 < two_k {
      nb[i2] = k.mul(nb[i2], half)
      i2 += 1
    }
    b = nb
    prec = two_k
  }
  b
}

///|
/// Formal derivative of a truncated series: `(i a_i) t^{i-1}`.
pub fn series_deriv(k : Fp, s : Series, n : Int32) -> Series {
  let out = Array::make(n, 0)
  let mut i = 1
  while i < n {
    if i < s.length() {
      out[i - 1] = k.mul(s[i], k.norm(i))
    }
    i += 1
  }
  out
}

///|
/// `a^e (mod t^n)` by square-and-multiply over truncated products:
/// `O(log e)` multiplications instead of `e`.
fn series_pow(k : Fp, a : Series, e : Int32, n : Int32) -> Series {
  let mut acc : Series = [1]
  let mut base = trunc(a, n)
  let mut kk = e
  while kk > 0 {
    if kk % 2 == 1 {
      acc = trunc(series_mul(k, acc, base, n), n)
    }
    base = trunc(series_mul(k, base, base, n), n)
    kk = kk / 2
  }
  trunc(acc, n)
}

///|
/// Newton iteration for the formal `m`-th root: solve `x^m = f` in
/// `K[[t]]/(t^N)`.
///
/// `g(x) = x^m - f`, `g'(x) = m x^{m-1}`, so the update is
/// `x <- x - (x^m - f) / (m x^{m-1})`; with the precision doubling of
/// `series_inv` the whole computation costs `O(log N)` truncated products
/// instead of the `N` of the naive "compute the first N terms one by one"
/// method.
///
/// **Convergence.**  If `x_k^m = f mod t^{2^k}` then `x_{k+1}^m = f mod t^{2^{k+1}}`:
/// writing `x_{k+1} = x_k(1 + eps)` with `eps in t^{2^k}`,
/// `x_{k+1}^m = f (1 + eps)^m = f (1 + m eps + O(eps^2)) = f mod t^{2^{k+1}}`.
pub fn series_root(
  k : Fp,
  f : Series,
  m : Int32,
  n : Int32,
  b0 : Int32,
) -> Series {
  if n == 0 || m < 1 {
    return []
  }
  // Newton needs `b0^m = f(0)` to start; otherwise the iteration diverges and
  // the caller would silently get a meaningless series.
  let start = trunc(series_pow(k, [b0], m, 1), 1)
  if start[0] != k.norm(coef(f, 0)) {
    return Array::make(n, 0)
  }
  let mut x : Series = [b0]
  let mut prec = 1
  while prec < n {
    let two_k = if 2 * prec < n { 2 * prec } else { n }
    // g(x) = x^m - f.  `x^m` is formed by square-and-multiply: `O(log m)`
    // truncated products instead of the `m` of a naive accumulation, which is
    // the dominant cost for large roots.
    let pw = series_pow(k, x, m, two_k)
    let g = Array::make(two_k, 0)
    let mut i = 0
    while i < two_k {
      g[i] = k.norm(coef(pw, i) - coef(f, i))
      i += 1
    }
    // g'(x) = m x^(m-1), same trick
    let pwm1 = series_pow(k, x, m - 1, two_k)
    let mcoef = k.norm(m)
    let dser = trunc(series_mul(k, pwm1, [mcoef], two_k), two_k)
    let dinv = series_inv(k, dser, two_k)
    let step = trunc(series_mul(k, g, dinv, two_k), two_k)
    let nx = Array::make(two_k, 0)
    let mut i3 = 0
    while i3 < two_k {
      nx[i3] = k.norm(coef(x, i3) - step[i3])
      i3 += 1
    }
    x = nx
    prec = two_k
  }
  x
}
