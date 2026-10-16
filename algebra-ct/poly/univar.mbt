///|
/// # Univariate factorization over `K = GF(p)`
///
/// Used by every 0-dimensional structure in the engine: the residue field of a
/// point `K[x]/(f_i)`, the idempotent decomposition of a finite ring, and the
/// minimal primes of an Artinian ideal.
///
/// **Algorithm.**
/// 1. *Radical part*: `rad(f) = f / gcd(f,f')^inf`.  The fixed point is
///    reached after at most `log_2 deg f` divisions because each pass divides
///    the degree by at least two.
/// 2. *Distinct-degree* on the square-free part:
///    `gcd(x^(p^d) - x, rad) = prod_{deg q = d} q`, evaluated by iterating
///    `a <- a^p mod rad`, i.e. `O(d log p)` modular multiplications.
/// 3. *Equal-degree split* (Cantor-Zassenhaus):
///    `gcd((x+c)^((p^d-1)/2) - 1, q)` splits `q` for a suitable `c`.
///
/// **Determinism.** Cantor-Zassenhaus normally draws `c` at random; here `c`
/// runs deterministically over `0, 1, 2, ...`.  This is complete (for each
/// conjugate pair some `c` separates it) and reproducible, which is mandatory
/// because the results are frozen into committed source code.

///|
/// `(irreducible factor, multiplicity)`.
pub type Factor = (Poly, Int32)

///|
/// Degree of a univariate polynomial (`-1` for the zero polynomial).
pub fn Poly::deg1(self : Poly) -> Int32 {
  self.univ_degree()
}

///|
/// Monic gcd in `K[x]` by the Euclidean algorithm.
///
/// The modulus is taken from the polynomials themselves (`a.k`), so the two
/// arguments must live in the same field; a caller passing a third, different
/// `Fp` used to be silently ignored.
pub fn gcd_univar(a : Poly, b : Poly) -> Poly {
  let mut x = a.monic(Lex)
  let mut y = b.monic(Lex)
  while !y.is_zero() {
    let (_, r) = x.divrem(y, Lex)
    x = y
    y = r
  }
  x
}

///|
/// `a^e mod m` by square-and-multiply: `O(log e)` modular multiplications.
pub fn pow_mod_univar(a : Poly, e : Int32, m : Poly) -> Poly {
  let mut base = a.divrem(m, Lex).1
  let mut acc = Poly::one_n(a.k, 1)
  let mut n = e
  while n > 0 {
    if n % 2 == 1 {
      acc = acc.mul(base).divrem(m, Lex).1
    }
    base = base.mul(base).divrem(m, Lex).1
    n = n / 2
  }
  acc
}

///|
/// The square-free radical `rad(f) = prod_{p | f} p`.
///
/// **Invariant.** `gcd(f, f') = f / rad(f)` whenever `char K` divides none of
/// the exponents, so each pass `g <- g / gcd(g, g')` peels one layer of
/// multiplicity off *every* factor at once.  Taking the running `lcm` of the
/// peeled layers -- rather than the last survivor -- is what makes the result
/// the radical and not just the last factor left standing.  Each pass drops
/// the degree by at least one, so the loop runs `O(log deg f)` times.
pub fn radical_part(f : Poly) -> Poly {
  let k = f.k
  let mut g = f.monic(Lex)
  let mut rad = Poly::one_n(k, 1)
  let mut go = g.deg1() > 0
  while go {
    let d = gcd_univar(g, g.derivative(0))
    if d.deg1() <= 0 {
      rad = lcm_univar(rad, g)
      go = false
    } else {
      g = g.divrem(d, Lex).0.monic(Lex)
      rad = lcm_univar(rad, g)
    }
  }
  rad.monic(Lex)
}

///|
/// Monic lcm of two univariate polynomials.
pub fn lcm_univar(a : Poly, b : Poly) -> Poly {
  if a.is_zero() {
    return b.monic(Lex)
  }
  if b.is_zero() {
    return a.monic(Lex)
  }
  let d = gcd_univar(a, b)
  if d.deg1() <= 0 {
    return a.mul(b).monic(Lex)
  }
  a.mul(b).divrem(d, Lex).0.monic(Lex)
}

///|
/// All linear factors `x - a` dividing `f`, found by evaluation at every
/// `a in K`.  Complete by construction, and cheaper than any splitting
/// heuristic because it needs no exponentiation at all: `O(p * deg f)`.
pub fn split_linear(k : Fp, f : Poly) -> Array[Poly] {
  let out : Array[Poly] = []
  let mut a = 0
  while a < k.p {
    let l = lin(k, a)
    if f.divrem(l, Lex).1.is_zero() {
      out.push(l)
    }
    a = a + 1
  }
  out
}

///|
/// A deterministic pseudo-random trial polynomial of degree `< d`.
fn trial_element(k : Fp, d : Int32, seed : Int32) -> Poly {
  let mut st = (seed * 48271 + 11) % k.p
  let pairs : Array[MTerm] = []
  let mut i = 0
  while i < d {
    st = (st * 16807 + 7) % k.p
    if st != 0 {
      pairs.push(([i], st))
    }
    i = i + 1
  }
  Poly::from_pairs(k, 1, pairs)
}

///|
/// Split a square-free polynomial whose irreducible factors all have degree
/// `d` (Cantor-Zassenhaus).
///
/// For `d = 1` the split is exhaustive root extraction.  For `d >= 2` the
/// trial element must have degree `< d`; a one-parameter family such as `x+c`
/// is provably insufficient, so the trials come from a fixed-seed linear
/// congruential generator.  Seeding makes the whole pipeline reproducible,
/// which matters because the factorizations are frozen into committed source.
fn equal_degree_split(k : Fp, f : Poly, d : Int32) -> Array[Poly] {
  if f.deg1() <= d {
    return [f]
  }
  if d == 1 {
    return split_linear(k, f)
  }
  // Cantor-Zassenhaus uses the exponent `(p^d - 1)/2` **mod p**.  Since `p`
  // is odd, `p^d = p * p^{d-1}` with `p^{d-1}` odd, so `p^d = 2pt + p` and
  // `(p^d - 1)/2 = pt + (p-1)/2  ==  (p-1)/2  (mod p)` for every `d >= 1`.
  // Computing `p^d` directly would overflow `Int32` already at `d = 5`.
  let e = (k.p - 1) / 2
  let mut tries = 0
  while tries < 512 {
    let a = trial_element(k, d, tries + 1)
    let b = pow_mod_univar(a, e, f).sub(Poly::one_n(k, 1))
    let g = gcd_univar(f, b)
    if g.deg1() > 0 && g.deg1() < f.deg1() {
      return equal_degree_split(k, g, d) +
        equal_degree_split(k, f.divrem(g, Lex).0, d)
    }
    tries += 1
  }
  [f]
}

///|
/// `x + c`.
pub fn Poly::add_const_public(self : Poly, c : Int32) -> Poly {
  let out = self.copy()
  out.add_term_mono(mono_zero(self.n), c)
  out
}

///|
/// Full factorization: distinct irreducible factors with multiplicities, so
/// `f = prod c_i^(m_i)` with the `c_i` pairwise coprime and irreducible.
pub fn factor_univar(k : Fp, f : Poly) -> Array[Factor] {
  let f = f.monic(Lex)
  if f.is_zero() || f.deg1() <= 0 {
    return []
  }
  let rad = radical_part(f)
  let distinct = distinct_irreducible(k, rad)
  let out : Array[Factor] = []
  for r in distinct {
    // multiplicity = max m with r^m | f, tested by exact division only
    let mut h = f
    let mut m = 0
    let mut go = true
    while go {
      let (q, rem) = h.divrem(r, Lex)
      if rem.is_zero() && !q.is_zero() {
        h = q
        m += 1
      } else {
        go = false
      }
    }
    if m > 0 {
      out.push((r, m))
    }
  }
  out.sort_by((x, y) => x.0.deg1() - y.0.deg1())
  out
}

///|
/// Distinct irreducible factors of a monic square-free polynomial.
pub fn distinct_irreducible(k : Fp, rad : Poly) -> Array[Poly] {
  let deg = rad.deg1()
  let out : Array[Poly] = []
  if deg <= 0 {
    return out
  }
  let mut cur = rad
  let mut a = Poly::var_n(k, 1, 0)
  let mut d = 1
  while 2 * d <= deg {
    a = pow_mod_univar(a, k.p, cur)
    let h = a.sub(Poly::var_n(k, 1, 0))
    let gg = gcd_univar(cur, h)
    if gg.deg1() > 0 {
      // `gg = cur` happens exactly when every remaining factor has degree `d`
      if gg.deg1() == cur.deg1() {
        for q in equal_degree_split(k, cur, d) {
          out.push(q)
        }
        cur = Poly::one_n(k, 1)
      } else {
        for q in equal_degree_split(k, gg, d) {
          out.push(q)
        }
        cur = cur.divrem(gg, Lex).0.monic(Lex)
      }
    }
    d += 1
  }
  if cur.deg1() > 0 {
    out.push(cur)
  }
  out.sort_by((x, y) => x.deg1() - y.deg1())
  out
}

///|
/// All roots of `f` inside `K`; the degree-1 layer of `factor_univar`.
pub fn roots_in_field(k : Fp, f : Poly) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut a = 0
  while a < k.p {
    if f.eval_at([a]) == 0 {
      out.push(a)
    }
    a += 1
  }
  out
}

///|
/// `x - a`.
pub fn lin(k : Fp, a : Int32) -> Poly {
  Poly::var_n(k, 1, 0).add_const_public(k.neg(a))
}
