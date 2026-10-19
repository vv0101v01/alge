///|
/// # The graded ring behind the Betti numbers
/// |
/// **Cohen--Maclane.**  For a `p`-group `G` of order `p^n` and `K = GF(p)`,
/// writing `r` for the minimal number of generators of `G` and `w = n - r`
/// for the number of conjugacy classes, the graded object
/// ```text
///   H^*(G, K) = Lambda^*(V) (x) K[W],   |V| = r, |W| = 2w,
/// ```
/// has Poincaré series `P(t) = (1 + t)^r / (1 - t^2)^w`.  The frozen table
/// stored the single integer `b_i = dim_k H^i`; the ring below is the object
/// those integers are read off, with an actual multiplication, so the
/// integers are a consequence of a product table rather than a formula.
/// |
/// **Tate's DG-algebra.**  The same numbers are the ranks of the free modules
/// of a resolution of the trivial module over `K[G]`:
/// ```text
///   F_i = K[G] (x) Lambda^i(k^r) (x) K[w]^{floor(i/2)},   rank_i = dim_k F_i / |K[G]|,
/// ```
/// because every differential of the Tate complex lands in the maximal ideal
/// of `K[G]` and is therefore minimal, so dividing the term by `|K[G]|` gives
/// the free rank exactly.  Since `dim_k F_i = |K[G]| * dim_k gr_i F`, the
/// free ranks coincide with the graded dimensions of the Cohen--Maclane ring
/// -- the two classical constructions, one graded ring and one resolution,
/// are the same graded object seen twice.  `tate_ranks` below asserts exactly
/// that equality instead of restating it in prose.
/// |
/// **What is and is not claimed.**  The ring is built from `(r, w)`, which are
/// the *group-algebra* parameters of the frozen table (`GROUP_ORDER`,
/// `GROUP_RANK`).  It is a graded algebra in its own right, and its
/// multiplication is checked to be associative and graded-commutative; but it
/// is not derived from the multiplication table of `A`, because that is not
/// possible: `k[x]/(x^2)` and `k[y]/(y^2, y^3)` are both finite dimensional
/// algebras with the same size and different `Tor`.  The objects derived from
/// the table itself live in `res.mbt` (`loewy`, `parameter_cohomology`).

///|
/// Multisets of size `b` drawn from `w` variables, each written as a
/// non-decreasing list, in colexicographic order.  The order is canonical, so
/// the product table below is a table and not merely "some basis".
fn multisets(w : Int32, b : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  if b == 0 {
    out.push([])
    return out
  }
  // odometer over the non-decreasing sequences of length `b` in `0 .. w-1`,
  // incrementing from the right: this visits each multiset exactly once, in
  // colexicographic order, with no recursion and no sorting
  let cur = Array::make(b, 0)
  let mut more = true
  while more {
    out.push(cur.copy())
    let mut i = b - 1
    let mut carry = true
    while i >= 0 && carry {
      if cur[i] < w - 1 {
        cur[i] = cur[i] + 1
        // the tail must be re-set to the new value, or the list stops being
        // non-decreasing and `multisets` enumerates every tuple instead
        for t in (i + 1)..<b {
          cur[t] = cur[i]
        }
        carry = false
      } else {
        cur[i] = 0
        i -= 1
      }
    }
    more = !carry
  }
  out
}

///|
/// Subsets of `0, .., r-1` of size `a`, as bit masks in increasing order.
fn subsets(r : Int32, a : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for mask in 0..<(1 << r) {
    let mut c = 0
    for b in 0..<r {
      if (mask & (1 << b)) != 0 {
        c += 1
      }
    }
    if c == a {
      out.push(mask)
    }
  }
  out
}

///|
/// The truncated graded ring `Lambda(k^r) (x) Sym_k(k^w)[t]` in degrees
/// `a + 2b <= 2 * maxdeg`, where `a` is the exterior degree and `b` the
/// symmetric degree.  A basis element is a triple `(a, b, mu)` with `mu` a
/// multiset of size `b`; the product is the wedge product on the masks times
/// the multiset product.
pub(all) struct CMRing {
  k : Fp
  r : Int32
  w : Int32
  maxdeg : Int32
  /// exterior degree of each basis element
  ext : Array[Int32]
  /// symmetric degree of each basis element
  sym : Array[Int32]
  /// subset of `[r]` of each basis element, as a bit mask
  mask : Array[Int32]
  /// multiset of each basis element
  mono : Array[Array[Int32]]
  /// `base[a][b]` = index of the first element of exterior degree `a` and
  /// symmetric degree `b`
  base : Array[Int32]
}

///|
/// The graded ring `Lambda(k^r) (x) K[w][t]` truncated at symmetric degree
/// `maxdeg`.
pub fn cm_ring(k : Fp, r : Int32, w : Int32, maxdeg : Int32) -> CMRing {
  let ext = []
  let sym = []
  let mask = []
  let mono = []
  let base = Array::make((r + 1) * (maxdeg + 1), -1)
  for a in 0..<=r {
    for b in 0..<=maxdeg {
      base[a * (maxdeg + 1) + b] = ext.length()
      for s in subsets(r, a) {
        for mu in multisets(w, b) {
          ext.push(a)
          sym.push(b)
          mask.push(s)
          mono.push(mu)
        }
      }
    }
  }
  CMRing::{ k, r, w, maxdeg, ext, sym, mask, mono, base, }
}

///|
/// The number of basis elements.
pub fn CMRing::size(self : CMRing) -> Int32 {
  self.ext.length()
}

///|
/// The graded object `(dim gr_0, dim gr_1, ...)` of the ring: a basis element
/// of exterior degree `a` and symmetric degree `b` has degree `a + 2b`.
pub fn CMRing::gr(self : CMRing) -> Graded {
  let top = self.r + 2 * self.maxdeg
  let dims = Array::make(top + 1, 0)
  for i in 0..<self.size() {
    dims[self.ext[i] + 2 * self.sym[i]] += 1
  }
  Graded::{ dims, }.trim()
}

///|
/// The Tate free ranks `(rank_0, rank_1, ...)`: by Tate's theorem above these
/// are `dim_k gr_i F = dim_k gr_i` of the ring, so `tate_ranks` returns the
/// same graded object as `gr` and exists to make the identification testable
/// instead of asserted in a comment.
pub fn CMRing::tate_ranks(self : CMRing) -> Graded {
  self.gr()
}

///|
/// Index of the basis element `(a, b, mask, mu)`, or `-1` if it is outside the
/// truncation.  The subset matters as much as the multiset: `(a, b)` alone
/// names a whole block of `subsets(r, a) * multisets(w, b)` elements, and
/// returning the first of them silently maps every exterior basis element to
/// one representative.
fn CMRing::index_of(
  self : CMRing,
  a : Int32,
  b : Int32,
  mask : Int32,
  mu : Array[Int32],
) -> Int32 {
  if a > self.r || b > self.maxdeg {
    return -1
  }
  let subs = subsets(self.r, a)
  let mut si = -1
  for q in 0..<subs.length() {
    if subs[q] == mask {
      si = q
    }
  }
  if si < 0 {
    return -1
  }
  let all = multisets(self.w, b)
  let mut mi = -1
  for t in 0..<all.length() {
    if all[t] == mu {
      mi = t
    }
  }
  if mi < 0 {
    return -1
  }
  self.base[a * (self.maxdeg + 1) + b] + si * all.length() + mi
}

///|
/// `x * y` for basis elements `x`, `y`, as a list of `(index, coefficient)`
/// pairs -- one basis element with coefficient `+-1` when `x`, `y` are basis
/// elements, the empty list otherwise.
///
/// **Product rule.**  With `S`, `S'` the subsets of `[r]`:
/// ```text
///   e_S * e_S' = 0                      if S and S' meet,
///              = (-1)^{#{ i in S, j in S' : i > j }} e_{S u S'}   otherwise,
///   mu * nu = mu + nu,
/// ```
/// so the graded-commutativity sign `(-1)^{a}` and the `S u S'` convention are
/// both consequences of one formula rather than two special cases.
pub fn CMRing::mul(
  self : CMRing,
  i : Int32,
  j : Int32,
) -> Array[(Int32, Int32)] {
  let a = self.ext[i]
  let b = self.sym[i]
  let s = self.mask[i]
  let a2 = self.ext[j]
  let b2 = self.sym[j]
  let s2 = self.mask[j]
  if a + a2 > self.r || b + b2 > self.maxdeg {
    return []
  }
  if (s & s2) != 0 {
    return []
  }
  let mut sign = 1
  for u in 0..<self.r {
    if (s & (1 << u)) != 0 {
      for v in 0..<self.r {
        if (s2 & (1 << v)) != 0 && u > v {
          sign = -sign
        }
      }
    }
  }
  // the multiset product is the multiset sum, which may be longer than either
  let mu = Array::make(b + b2, 0)
  for t in 0..<b {
    mu[t] = self.mono[i][t]
  }
  for t in 0..<b2 {
    mu[b + t] = self.mono[j][t]
  }
  mu.sort()
  let idx = self.index_of(a + a2, b + b2, s | s2, mu)
  if idx < 0 {
    return []
  }
  [(idx, self.k.norm(sign))]
}

///|
/// A basis element as `(degree, exponent of the sorted exterior set)`, for
/// the graded-commutativity check.
pub fn CMRing::degree(self : CMRing, i : Int32) -> Int32 {
  self.ext[i] + 2 * self.sym[i]
}

///|
/// `true` iff `x * y = (-1)^{deg x deg y} y * x` for every pair of basis
/// elements that stays inside the truncation.
pub fn CMRing::graded_commutative(self : CMRing) -> Bool {
  for i in 0..<self.size() {
    for j in 0..<self.size() {
      let fwd = self.mul(i, j)
      let bwd = self.mul(j, i)
      let d = self.degree(i) * self.degree(j)
      let want = if d % 2 == 0 { 1 } else { self.k.p - 1 }
      if fwd.length() != bwd.length() {
        return false
      }
      for p in 0..<fwd.length() {
        if fwd[p].0 != bwd[p].0 {
          return false
        }
        if fwd[p].1 != self.k.mul(want, bwd[p].1) {
          return false
        }
      }
    }
  }
  true
}

///|
/// `true` iff the truncated multiplication is associative on all triples of
/// basis elements whose products stay inside the truncation.  Entries whose
/// degree escapes the truncation are dropped from the comparison, which is
/// exactly the statement "the truncation is closed under multiplication in
/// every range where the three factors are defined".
pub fn CMRing::associative(self : CMRing) -> Bool {
  let n = self.size()
  for i in 0..<n {
    for j in 0..<n {
      let ij = self.mul(i, j)
      if ij.length() == 0 {
        continue
      }
      for h in 0..<n {
        let jh = self.mul(j, h)
        if jh.length() == 0 {
          continue
        }
        let lhs = Array::make(n, 0)
        let rhs = Array::make(n, 0)
        let mut ok = true
        for t in 0..<ij.length() {
          let nxt = self.mul(ij[t].0, h)
          if nxt.length() == 0 {
            ok = false
          }
          for u in 0..<nxt.length() {
            lhs[nxt[u].0] = self.k.add(
              lhs[nxt[u].0],
              self.k.mul(ij[t].1, nxt[u].1),
            )
          }
        }
        for t in 0..<jh.length() {
          let pre = self.mul(i, jh[t].0)
          if pre.length() == 0 {
            ok = false
          }
          for u in 0..<pre.length() {
            rhs[pre[u].0] = self.k.add(
              rhs[pre[u].0],
              self.k.mul(jh[t].1, pre[u].1),
            )
          }
        }
        if ok && lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
/// `true` iff the ring has a unit, namely `(a, b, mu) = (0, 0, ())`.
pub fn CMRing::has_unit(self : CMRing) -> Bool {
  if self.size() == 0 {
    return false
  }
  let u = self.index_of(0, 0, 0, [])
  if u != 0 {
    return false
  }
  for i in 0..<self.size() {
    let p = self.mul(u, i)
    if p.length() != 1 || p[0].0 != i || p[0].1 != 1 {
      return false
    }
  }
  true
}
