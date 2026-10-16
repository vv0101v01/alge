///|
/// # The coordinate ring `R = K[x_1, ..., x_n]` as a sparse map
///
/// **Definition.** A polynomial of `R` is a finite `K`-linear combination of
/// monomials; it is stored *uniquely* as the map `monomial -> K` restricted to
/// non-zero coefficients.  Because `N^n` is free (see `mono.mbt`) that map is
/// a canonical form, so polynomial equality is `Map` equality and no separate
/// normalisation step is ever needed.
///
/// **Cost model.** `d = #terms(f)`, `e = #terms(g)`.
/// - `add`, `sub`: `O(d + e)` hash operations.
/// - `mul`: `O(d * e)` hash operations -- the product monomial is computed per
///   pair, which is the reason the emitted runtime code avoids polynomial
///   multiplication altogether (§ quotient multiplication tables).
/// - `divrem` against a single `g`: one `lead` + one `inv` + one `mul` +
///   one `sub` per cancellation step, i.e. `O(L * (d+e))` for `L` steps.

///|
/// A monomial together with its coefficient.
pub type MTerm = (Array[Int32], Int32)

///|
///
/// **No `Eq` derive.** `==` on a record compares the backing `Map` by
/// reference, so `f == g` would silently answer "same object" instead of
/// "same polynomial".  Use `Poly::same`, which compares the canonical sparse
/// forms term by term.
pub(all) struct Poly {
  k : Fp
  n : Int32
  terms : Map[String, Int32]
}

///|
/// The zero polynomial carries the ring dimension, so `n` is explicit: the
/// coordinate ring of `A^0` is `K` itself, which is *not* the zero ring, and
/// conflating the two would silently break every zero-dimensional case.
pub fn Poly::zero_n(k : Fp, n : Int32) -> Poly {
  { k, n, terms: Map([]), }
}

///|
pub fn Poly::one_n(k : Fp, n : Int32) -> Poly {
  let p = Poly::zero_n(k, n)
  p.add_term_mono(mono_one(n), 1)
  p
}

///|
/// A constant of the ring.
pub fn Poly::const_n(k : Fp, n : Int32, c : Int32) -> Poly {
  let p = Poly::zero_n(k, n)
  p.add_term_mono(mono_zero(n), c)
  p
}

///|
/// The variable `x_i` of the coordinate ring `K[x_0, ..., x_{n-1}]`.
pub fn Poly::var_n(k : Fp, n : Int32, i : Int32) -> Poly {
  let p = Poly::zero_n(k, n)
  p.add_term_mono(mono_var(n, i), 1)
  p
}

///|
pub fn Poly::from_mono(k : Fp, n : Int32, m : Array[Int32], c : Int32) -> Poly {
  let p = Poly::zero_n(k, n)
  p.add_term_mono(m, c)
  p
}

///|
/// Internal: accumulate a term, deleting it when the coefficient cancels.
/// Keeping the map free of zeros is the only invariant the rest of the engine
/// relies on, so it is enforced here once and for all.
fn Poly::add_term_mono(self : Poly, m : Array[Int32], c : Int32) -> Unit {
  let cc = self.k.norm(c)
  if cc == 0 {
    ()
  } else {
    let key = mono_key(m)
    match self.terms.get(key) {
      None => self.terms.set(key, cc)
      Some(old) => {
        let s = self.k.norm(old + cc)
        if s == 0 {
          self.terms.remove(key)
        } else {
          self.terms.set(key, s)
        }
      }
    }
  }
}

///|
/// Fresh map with the same content (safe to mutate afterwards).
pub fn Poly::copy(self : Poly) -> Poly {
  let t : Map[String, Int32] = Map([])
  for kv in self.terms {
    t.set(kv.0, kv.1)
  }
  { k: self.k, n: self.n, terms: t, }
}

///|
pub fn Poly::is_zero(self : Poly) -> Bool {
  self.terms.length() == 0
}

///|
pub fn Poly::num_terms(self : Poly) -> Int32 {
  self.terms.length()
}

///|
pub fn Poly::add(self : Poly, other : Poly) -> Poly {
  let out = self.copy()
  for kv in other.terms {
    out.add_term_mono(mono_parse(kv.0), kv.1)
  }
  out
}

///|
pub fn Poly::sub(self : Poly, other : Poly) -> Poly {
  let out = self.copy()
  for kv in other.terms {
    out.add_term_mono(mono_parse(kv.0), self.k.neg(kv.1))
  }
  out
}

///|
pub fn Poly::neg(self : Poly) -> Poly {
  self.scale(self.k.neg(1))
}

///|
pub fn Poly::scale(self : Poly, c : Int32) -> Poly {
  let out = Poly::zero_n(self.k, self.n)
  for kv in self.terms {
    out.add_term_mono(mono_parse(kv.0), self.k.mul(c, kv.1))
  }
  out
}

///|
/// Divide every coefficient by `c` (`c != 0`); used to keep a Gröbner basis
/// monic, which removes one modular inversion per cancellation step later on.
pub fn Poly::scale_inv(self : Poly, c : Int32) -> Poly {
  self.scale(self.k.inv(c))
}

///|
pub fn Poly::mul(self : Poly, other : Poly) -> Poly {
  let out = Poly::zero_n(self.k, self.n)
  for kv in self.terms {
    let m = mono_parse(kv.0)
    for kv2 in other.terms {
      out.add_term_mono(mono_mul(m, mono_parse(kv2.0)), self.k.mul(kv.1, kv2.1))
    }
  }
  out
}

///|
/// Terms sorted *decreasingly* by the given monomial order, so `arr[0]` is the
/// leading term.  Sorting is `O(d log d)` and makes every downstream traversal
/// deterministic regardless of `Map` iteration order.
pub fn Poly::sorted(self : Poly, order : Order) -> Array[MTerm] {
  let arr : Array[MTerm] = []
  for kv in self.terms {
    arr.push((mono_parse(kv.0), kv.1))
  }
  arr.sort_by((x, y) => -cmp_mono(order, x.0, y.0))
  arr
}

///|
/// Leading term `(monomial, coefficient)`, i.e. the `0`-th entry of
/// `sorted`.
///
/// **Complexity.** `O(d)` comparisons, against `O(d log d)` for sorting the
/// whole polynomial: `lead` sits inside the innermost loop of `divrem`,
/// `normal_form` and `s_poly`, where the extra `log d` factor is pure loss.
pub fn Poly::lead(self : Poly, order : Order) -> MTerm {
  let mut best : MTerm = (mono_zero(self.n), 0)
  let mut first = true
  for kv in self.terms {
    let m = mono_parse(kv.0)
    if first || cmp_mono(order, m, best.0) > 0 {
      best = (m, kv.1)
      first = false
    }
  }
  best
}

///|
/// Leading *monomial*.
pub fn Poly::lead_mono(self : Poly, order : Order) -> Array[Int32] {
  self.lead(order).0
}

///|
/// `f * m` for a monomial `m`.
pub fn Poly::mul_mono(self : Poly, m : Array[Int32]) -> Poly {
  let out = Poly::zero_n(self.k, self.n)
  for kv in self.terms {
    out.add_term_mono(mono_mul(mono_parse(kv.0), m), kv.1)
  }
  out
}

///|
/// Public fluent wrapper around `add_term_mono`: returns a copy with the term
/// `c * m` accumulated.
pub fn Poly::add_term_public(self : Poly, m : Array[Int32], c : Int32) -> Poly {
  let out = self.copy()
  out.add_term_mono(m, c)
  out
}

///|
/// Monic normal form: `f / lc(f)`.
pub fn Poly::monic(self : Poly, order : Order) -> Poly {
  if self.is_zero() {
    self
  } else {
    let (_, c) = self.lead(order)
    self.scale_inv(c)
  }
}

///|
/// `s`-polynomial of `f` and `g` (both monic):
/// `S(f,g) = x^L/lm(f) * f - x^L/lm(g) * g` with `L = lcm(lm(f), lm(g))`.
/// This is the single object Buchberger's algorithm must reduce to zero.
pub fn Poly::s_poly(self : Poly, other : Poly, order : Order) -> Poly {
  let (lm, lc) = self.lead(order)
  let (lm2, lc2) = other.lead(order)
  let l = mono_lcm(lm, lm2)
  let q1 = mono_div(l, lm).unwrap_or(mono_zero(self.n))
  let q2 = mono_div(l, lm2).unwrap_or(mono_zero(self.n))
  let a = self.mul_mono(q1).scale(self.k.inv(lc))
  let b = other.mul_mono(q2).scale(self.k.inv(lc2))
  a.sub(b)
}

///|
/// Multivariate division by one divisor `g != 0`.
/// **Lemma (termination).** Each cancellation strictly decreases `r` in the
/// monomial order, which is well founded, so the loop stops after at most
/// `#terms(f)` steps.
pub fn Poly::divrem(self : Poly, g : Poly, order : Order) -> (Poly, Poly) {
  let q = Poly::zero_n(self.k, self.n)
  let mut r = self.copy()
  let (gl, gc) = g.lead(order)
  let inv_gc = if gc == 1 { 1 } else { self.k.inv(gc) }
  let mut stop = false
  while !stop && !r.is_zero() {
    let (rl, rc) = r.lead(order)
    match mono_div(rl, gl) {
      None => stop = true
      Some(qm) => {
        let f = self.k.mul(rc, inv_gc)
        q.add_term_mono(qm, f)
        r = r.sub(Poly::from_mono(self.k, self.n, qm, f).mul(g))
      }
    }
  }
  (q, r)
}

///|
/// Multivariate division by a list `(g_1, ..., g_s)`: returns `q` and the
/// canonical remainder `r` with `deg r < deg g_i` for all `i`.
pub fn Poly::divrem_list(
  self : Poly,
  gs : Array[Poly],
  order : Order,
) -> (Array[Poly], Poly) {
  let qs : Array[Poly] = []
  let mut r = self.copy()
  for g in gs {
    if g.is_zero() {
      qs.push(Poly::zero_n(self.k, self.n))
    } else {
      let (q, r2) = r.divrem(g, order)
      qs.push(q)
      r = r2
    }
  }
  (qs, r)
}

///|
/// Canonical remainder of `f` modulo `<gs>`, i.e. the **normal form**
/// `NF(f)`.
///
/// **Algorithm.** At every step pick the `g` whose leading monomial divides
/// `LM(r)` *and is largest among those*, then cancel.  Choosing "largest
/// among the divisors" is what makes the result order-independent, hence the
/// genuine normal form: after the loop no monomial of `r` is divisible by any
/// `LM(g)`.
///
/// **Why dividing by the basis in a fixed order is wrong.** With
/// `G = {x^2 - y, y^2 - 1}` and `f = x^2 - y^3`, dividing first by `x^2 - y`
/// (which cannot cancel `y^3`) and then by `y^2 - 1` stops at `x^2 - y != 0`,
/// even though `f in <G>`.  The largest-divisor rule instead cancels `y^3`
/// first and reaches `0`.  Every reduction step strictly decreases `r` in the
/// well-founded monomial order, so the loop terminates.
pub fn Poly::normal_form(self : Poly, gs : Array[Poly], order : Order) -> Poly {
  let mut r = self.copy()
  let mut go = true
  while go && !r.is_zero() {
    go = false
    let (rl, rc) = r.lead(order)
    let mut best = -1
    let mut best_lm = mono_zero(self.n)
    for gi in 0..<gs.length() {
      let g = gs[gi]
      if !g.is_zero() {
        let gl = g.lead_mono(order)
        if mono_div_by(rl, gl) {
          if best < 0 || cmp_mono(order, gl, best_lm) > 0 {
            best = gi
            best_lm = gl
          }
        }
      }
    }
    if best >= 0 {
      let (_, gc) = gs[best].lead(order)
      let inv = if gc == 1 { 1 } else { self.k.inv(gc) }
      let qm = mono_div(rl, best_lm).unwrap_or(mono_zero(self.n))
      let f = self.k.mul(rc, inv)
      r = r.sub(Poly::from_mono(self.k, self.n, qm, f).mul(gs[best]))
      go = true
    }
  }
  r
}

///|
/// `true` iff `f` lies in the ideal generated by `gs`.
/// **Theorem (Buchberger / division criterion).** `f in I` iff `NF(f) = 0`.
/// This is the *only* membership test the engine ever uses; complexity drops
/// from an unbounded search over the ideal to one pass over the basis.
pub fn Poly::in_ideal(self : Poly, gs : Array[Poly], order : Order) -> Bool {
  self.normal_form(gs, order).is_zero()
}

///|
/// Formal derivative.  With `char K = p > maxdeg` every derivative is
/// `e_i * c * x^(e - 1)`, so no term is killed by the characteristic.
pub fn Poly::derivative(self : Poly, i : Int32) -> Poly {
  let out = Poly::zero_n(self.k, self.n)
  for kv in self.terms {
    let m = mono_parse(kv.0)
    if m[i] > 0 {
      let m2 = m.copy()
      m2[i] = m[i] - 1
      out.add_term_mono(m2, self.k.mul(kv.1, m[i]))
    }
  }
  out
}

///|
/// Evaluate at a point of `K^n`.
pub fn Poly::eval_at(self : Poly, pt : Array[Int32]) -> Int32 {
  let mut acc = 0
  for kv in self.terms {
    let m = mono_parse(kv.0)
    let mut c = kv.1
    let mut i = 0
    while i < self.n {
      let mut e = 0
      while e < m[i] {
        c = self.k.mul(c, pt[i])
        e += 1
      }
      i = i + 1
    }
    acc = self.k.add(acc, c)
  }
  acc
}

///|
/// Coefficient of a monomial, `0` if absent.
pub fn Poly::coeff(self : Poly, m : Array[Int32]) -> Int32 {
  self.terms.get(mono_key(m)).unwrap_or(0)
}

///|
/// True when `f` is a non-zero constant.
pub fn Poly::is_nonzero_constant(self : Poly) -> Bool {
  self.terms.length() == 1 && self.terms.contains(mono_key(mono_zero(self.n)))
}

///|
/// Value of a non-zero constant.
pub fn Poly::constant_value(self : Poly) -> Int32 {
  self.coeff(mono_zero(self.n))
}

///|
/// Univariate degree (only meaningful for `n = 1`).
pub fn Poly::univ_degree(self : Poly) -> Int32 {
  let mut d = -1
  for kv in self.terms {
    let m = mono_parse(kv.0)
    if m[0] > d {
      d = m[0]
    }
  }
  d
}

///|
/// Readable form, used for the emitted documentation tables.
pub fn Poly::show(self : Poly, order : Order) -> String {
  if self.is_zero() {
    return "0"
  }
  let arr = self.sorted(order)
  let parts : Array[String] = []
  for t in arr {
    let m = t.0
    let c = t.1
    let ms = mono_show(m)
    let head = if mono_eq(m, mono_zero(self.n)) {
      "\{c}"
    } else if c == 1 {
      ms
    } else if c == self.k.p - 1 {
      "-1*\{ms}"
    } else {
      "\{c}*\{ms}"
    }
    parts.push(head)
  }
  parts.join(" + ")
}

///|
/// Machine readable form `(exp-list, coeff)` pairs, used by the emitter.
pub fn Poly::pairs(self : Poly, order : Order) -> Array[MTerm] {
  self.sorted(order)
}

///|
/// Build a polynomial from explicit `(monomial, coefficient)` pairs.
pub fn Poly::from_pairs(k : Fp, n : Int32, pairs : Array[MTerm]) -> Poly {
  let p = Poly::zero_n(k, n)
  for t in pairs {
    p.add_term_mono(t.0, t.1)
  }
  p
}

///|
/// Substitute `x_i = a`.
pub fn Poly::subst(self : Poly, i : Int32, a : Int32) -> Poly {
  let out = Poly::zero_n(self.k, self.n)
  let aa = self.k.norm(a)
  for kv in self.terms {
    let m = mono_parse(kv.0)
    let mut c = kv.1
    let mut e = 0
    while e < m[i] {
      c = self.k.mul(c, aa)
      e += 1
    }
    let m2 = m.copy()
    m2[i] = 0
    out.add_term_mono(m2, c)
  }
  out
}

///|
/// Structural equality of two polynomials, comparing the canonical sparse
/// forms term by term.  `==` on the record would compare the backing `Map`
/// reference, which is *reference* equality, so the algebra must never use it.
pub fn Poly::same(self : Poly, other : Poly) -> Bool {
  if self.n != other.n || self.k.p != other.k.p {
    return false
  }
  if self.terms.length() != other.terms.length() {
    return false
  }
  for kv in self.terms {
    match other.terms.get(kv.0) {
      None => return false
      Some(v) => if v != kv.1 { return false }
    }
  }
  true
}
