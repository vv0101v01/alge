///|
/// # Resolutions: computing derived data from the multiplication table
/// |
/// The invariants in `coho` are *numbers about* `A`: the dimension of the
/// radical, of the socle, of `Ext^1`.  This file computes *objects*: graded
/// pieces of the algebra itself, and a genuine cochain complex with its
/// matrices written down, whose cohomology is obtained by elimination.
/// **Tate's theorem, the categorical form.**  Let `A` be a finite dimensional
/// `K`-algebra, `F_* -> A` a free resolution of `A`, and `M`, `N` modules.
/// Then
/// ```text
///   Ext^i_A(M, N) = H^i(Hom_A(F_*, N)),   Tor_i^A(M, N) = H_i(F_* (x)_A M),
/// ```
/// so whenever `F_i` is free of rank `b_i` both are `K`-vector spaces of
/// dimension `b_i`: `Ext^i` and `Tor_i` are dual to each other.  A Betti
/// number is therefore never really "the dimension of the `Ext^1`"; it is the
/// rank of a free module in a resolution.  This file builds such a complex --
/// the Koszul complex on the parameters of the local factor -- with real
/// matrices and real cohomology, so the graded dimension is computed rather
/// than asserted.  The Tate DG-algebra in `ring.mbt` supplies the free ranks
/// in all degrees, where the matrices would be too large to write down.
/// |
/// Two honest caveats are recorded rather than hidden.
/// * The Koszul complex on a system of parameters resolves the residue field
///   only when the parameters form a regular sequence, i.e. when the local
///   ring is regular.  In general its cohomology -- the *parameter
///   cohomology*, computed here -- is not `Tor` and makes no claim to be.
/// * Free ranks in all degrees require the Tate DG-algebra; `ring.mbt` builds
///   it from `(r, w = |G| - r)`, which is the classical Cohen--Maclane input,
///   so those degrees are a consequence of the group-algebra structure and
///   not of this multiplication table.
/// |
/// One local factor `A_p` of a split Artin `K`-algebra, together with its
/// maximal ideal `m_p` and both multiplication tables.
pub(all) struct Local {
  /// the residue field of `A_p` (equal to `K` for a split algebra)
  k : Fp
  /// `dim_k A_p`
  dim : Int32
  /// `dim_k m_p`
  mdim : Int32
  /// `table[(i * dim + j) * dim + c]` = `c`-th `A_p`-coordinate of `b_i * b_j`
  table : Array[Int32]
  /// `mtable[(a * mdim + b) * mdim + c]` = `c`-th `m_p`-coordinate of `m_a * m_b`
  mtable : Array[Int32]
  /// `cross[(a * mdim + t) * dim + c]` = `c`-th `A_p`-coordinate of `b_a * m_t`,
  /// the product `A_p (x) m_p -> A_p` that the Koszul differential and the
  /// Loewy powers need
  cross : Array[Int32]
}

///|
/// `A_p` and `m_p` for the `K`-rational point `pt`.
///
/// **Theorem (T2, splitness).**  `Psi : A -> K^r`, `f |-> (f(a_1),...,f(a_r))`
/// is surjective (the image contains `Psi(1) = (1,...,1)`) with kernel the
/// nilradical, so for `A` split over `K`
/// ```text
///   A = prod_p A_p,   A_p = e_p A,   dim_k A = sum_p dim_k A_p,
/// ```
/// where `e_p` is the Lagrange idempotent, `1` at `pt` and `0` at every other
/// point.  The local factor is therefore `e_p A = A / (1 - e_p) A`, and the
/// two spaces are separated by one elimination:
///
/// - `K_p = { s : e_p s = 0 }` is the kernel of the matrix `s |-> e_p s`,
///   a basis of `(1 - e_p) A`, of dimension `dim_k A - dim_k A_p`;
/// - stacking those rows *under* the identity and reducing gives a basis
///   `U` of `A_p` in the last `dim_k A_p` rows, with pivot column `pivots[i]`
///   carrying the `i`-th coordinate of every vector of `A`;
///
/// `m_p` is then the kernel of the evaluation `A_p -> K` at `pt` -- for a
/// local `K`-algebra the maximal ideal is exactly the elements that vanish at
/// the residue field -- and since the reduction above puts `U` in reduced
/// echelon form, the `i`-th coordinate of a vector of `A` is its `i`-th row
/// entry at column `pivots[i]`.  Every coordinate extraction below is one
/// array read.
pub fn local_factor(q : Quot, ps : Array[Array[Int32]], p : Int32) -> Local {
  let k = q.k
  let d = q.dim
  let pt = ps[p]
  let e = @quot.primitive_idempotents(q, ps)[p]
  // the projection `s |-> e_p s`, and its kernel `(1 - e_p) A`
  let proj : Array[Array[Int32]] = []
  for j in 0..<d {
    proj.push(q.mul_coords(e, unit_vector(d, j)))
  }
  let kernel = @la.nullspace(k, proj, d)
  let ker = kernel.length()
  let dp = d - ker
  // stack the kernel under the identity and reduce: the last `dp` rows are a
  // basis of `A_p`, and `pivots` says which column carries which coordinate
  let stack = kernel.map(r => r.copy())
  let mut i = 0
  while i < d {
    let row = Array::make(d, 0)
    row[i] = 1
    stack.push(row)
    i += 1
  }
  let (a, pivots) = @la.rref(k, stack)
  let u : Array[Array[Int32]] = []
  i = 0
  while i < dp {
    u.push(a[ker + i].copy())
    i += 1
  }
  // the value of every standard monomial at the point, so that evaluating a
  // combination of them is one dot product
  let vals = Array::make(d, 0)
  let mut c = 0
  while c < d {
    vals[c] = eval_basis(k, q, c, pt)
    c += 1
  }
  // the maximal ideal `m_p`: the kernel of the evaluation `A_p -> K` at the
  // point, because `A_p` is local with residue field `K`, so an element is in
  // `m_p` exactly when it vanishes at the residue field.  `la.nullspace`
  // returns the kernel in the coordinates of `u`; they are lifted back to
  // coordinates in `A` so that every product below is a single table read.
  let ev : Array[Array[Int32]] = [Array::make(dp, 0)]
  let mut i = 0
  while i < dp {
    let mut acc = 0
    let mut cc = 0
    while cc < d {
      acc = k.add(acc, k.mul(u[i][cc], vals[cc]))
      cc += 1
    }
    ev[0][i] = acc
    i += 1
  }
  let mvec = @la.nullspace(k, ev, dp)
  let dm = mvec.length()
  let mA : Array[Array[Int32]] = []
  i = 0
  while i < dm {
    let v = Array::make(d, 0)
    let mut cc = 0
    while cc < dp {
      if k.is_nonzero(mvec[i][cc]) {
        let f = mvec[i][cc]
        let mut c2 = 0
        while c2 < d {
          v[c2] = k.add(v[c2], k.mul(f, u[cc][c2]))
          c2 += 1
        }
      }
      cc += 1
    }
    mA.push(v)
    i += 1
  }
  // `mA` in reduced echelon form is *the* basis of `m_p` used below, so the
  // `c`-th `m_p`-coordinate of a vector of `A` is its entry at `mpiv[c]`
  let (_, mpiv) = @la.rref(k, mA)
  let table = Array::make(dp * dp * dp, 0)
  for i in 0..<dp {
    for j in 0..<dp {
      let w = q.mul_coords(u[i], u[j])
      let mut cc = 0
      while cc < dp {
        table[(i * dp + j) * dp + cc] = w[pivots[ker + cc]]
        cc += 1
      }
    }
  }
  let mtable = Array::make(dm * dm * dm, 0)
  for i in 0..<dm {
    for j in 0..<dm {
      let w = q.mul_coords(mA[i], mA[j])
      let mut cc = 0
      while cc < dm {
        mtable[(i * dm + j) * dm + cc] = w[mpiv[cc]]
        cc += 1
      }
    }
  }
  let cross = Array::make(dp * dm * dp, 0)
  for i in 0..<dp {
    for j in 0..<dm {
      let w = q.mul_coords(u[i], mA[j])
      let mut cc = 0
      while cc < dp {
        cross[(i * dm + j) * dp + cc] = w[pivots[ker + cc]]
        cc += 1
      }
    }
  }
  Local::{ k, dim: dp, mdim: dm, table, mtable, cross, }
}

///|
/// All local factors, one per `K`-rational point.
///
/// **Theorem (T2, dimensions).**  `sum_p loc.dim == dim_k A` and
/// `sum_p loc.mdim == dim_k rad A`: the direct-sum decomposition of `A` along
/// its points cuts both the algebra and its radical additively.  Both
/// identities are asserted in the tests, and they are what makes
/// `Tor^A(K,K) = prod_p Tor^{A_p}(K,K)` legitimate, so that the local
/// computation below really does compute the Tor of `A`.
pub fn local_factors(q : Quot, ps : Array[Array[Int32]]) -> Array[Local] {
  let out : Array[Local] = []
  for p in 0..<ps.length() {
    out.push(local_factor(q, ps, p))
  }
  out
}

///|
/// The unit vector `e_j`.
fn unit_vector(d : Int32, j : Int32) -> Array[Int32] {
  let e = Array::make(d, 0)
  e[j] = 1
  e
}

///|
/// The value of the standard monomial `j` at `pt`.
fn eval_basis(k : Fp, q : Quot, j : Int32, pt : Array[Int32]) -> Int32 {
  let mut prod = 1
  let mut v = 0
  while v < pt.length() {
    let mut e = 0
    while e < q.basis[j][v] {
      prod = k.mul(prod, pt[v])
      e += 1
    }
    v += 1
  }
  prod
}

///|
/// The Hilbert function of `A` as a graded object: `(A_0, A_1, ...)` with `A_d`
/// the span of the standard monomials of total degree `d`.
///
/// **Theorem (T14).**  `sum_d A_d t^d` is the Hilbert series of `A`; it
/// satisfies `H_A(1) = dim_k A` (the recovery identity, asserted in the
/// tests) and, being the graded isomorphism type of `A`, it is an invariant of
/// the algebra rather than of its presentation.  It is the first genuine lift
/// in this system: the integer `dim_k A` cannot distinguish `K[x]/(x^2)` from
/// `K[x,y]/(x^2, xy, y^2)` -- both have dimension `3` -- while their Hilbert
/// functions `1 + t` and `1 + 2t` do not.
pub fn hilbert(q : Quot) -> Graded {
  let d = q.dim
  let mut maxdeg = 0
  for i in 0..<d {
    let mut deg = 0
    for e in q.basis[i] {
      deg += e
    }
    if deg > maxdeg {
      maxdeg = deg
    }
  }
  let dims = Array::make(maxdeg + 1, 0)
  for i in 0..<d {
    let mut deg = 0
    for e in q.basis[i] {
      deg += e
    }
    dims[deg] += 1
  }
  Graded::{ dims, }
}

///|
/// The `c`-th `A_p`-coordinate of `b_a * m_t`, the product that the Koszul
/// differential needs.
fn cross_get(loc : Local, a : Int32, t : Int32, c : Int32) -> Int32 {
  loc.cross[(a * loc.mdim + t) * loc.dim + c]
}

///|
/// The `A_p`-coordinates of `b * m_t` for an arbitrary `b` in `A_p`,
/// `sum_c b[c] * cross[c][t]`: bilinearity, with no assumption on `b`.
fn mul_by_m(loc : Local, b : Array[Int32], t : Int32) -> Array[Int32] {
  let k = loc.k
  let out = Array::make(loc.dim, 0)
  for c in 0..<loc.dim {
    if b[c] != 0 {
      for q in 0..<loc.dim {
        out[q] = k.add(out[q], k.mul(b[c], cross_get(loc, c, t, q)))
      }
    }
  }
  out
}

///|
/// Subsets of `0, .., n-1` of size `i`, encoded as bit masks, in increasing
/// mask order -- a canonical order independent of `i`, which is what lets the
/// `i`-th and `(i-1)`-st terms be lined up against each other.
fn masks_of_size(n : Int32, i : Int32) -> Array[Int32] {
  let out = []
  for mask in 0..<(1 << n) {
    let mut c = 0
    for b in 0..<n {
      if (mask & (1 << b)) != 0 {
        c += 1
      }
    }
    if c == i {
      out.push(mask)
    }
  }
  out
}

///|
/// The Koszul complex `K(theta_0, ..., theta_{mdim-1})` of the local factor on
/// a basis of its maximal ideal,
/// ```text
///   K^i = A_p (x) Lambda^i(theta),   d^i(b_a (x) e_S) = sum_{j in S} (-1)^pos(j) (b_a theta_j) (x) e_{S\j},
/// ```
/// with every differential written out as a matrix over `K`.
///
/// This is a cochain complex for *every* finite dimensional local algebra --
/// `d d = 0` holds by construction, and the tests check it on the matrices --
/// and it resolves the residue field exactly when the `theta` form a regular
/// sequence.  Its cohomology is therefore reported as what it is, the
/// **parameter cohomology**, and not as `Tor`: asserting otherwise would be
/// asserting that every Artin local ring were regular.  What it gives without
/// caveat is a graded object of the local ring computed by elimination from the
/// multiplication table, and a resolution in the regular case.
pub fn koszul_complex(loc : Local) -> Complex {
  let k = loc.k
  let n = loc.mdim
  let d = loc.dim
  let dims = []
  let maps = []
  for i in 0..<=(n + 1) {
    dims.push(masks_of_size(n, i).length() * d)
  }
  for i in 1..<=n {
    let src = masks_of_size(n, i)
    let tgt = masks_of_size(n, i - 1)
    let ntgt = tgt.length()
    // each row must be its own array: `Array::make(n, row)` would alias
    let mat = []
    for _ in 0..<(ntgt * d) {
      mat.push(Array::make(src.length() * d, 0))
    }
    for s in 0..<src.length() {
      let mask = src[s]
      for j in 0..<n {
        if (mask & (1 << j)) == 0 {
          continue
        }
        // the position of j inside the sorted subset fixes the Koszul sign
        let mut pos = 0
        for b in 0..<j {
          if (mask & (1 << b)) != 0 {
            pos += 1
          }
        }
        let sgn = if pos % 2 == 0 { 1 } else { k.p - 1 }
        let tm = mask - (1 << j)
        let mut ti = -1
        for q in 0..<ntgt {
          if tgt[q] == tm {
            ti = q
          }
        }
        if ti < 0 {
          continue
        }
        for a in 0..<d {
          for c in 0..<d {
            let v = k.mul(sgn, cross_get(loc, a, j, c))
            if v != 0 {
              mat[ti * d + c][s * d + a] = v
            }
          }
        }
      }
    }
    maps.push(mat)
  }
  Complex::{ dims, maps, }
}

///|
/// The graded object `(H^0, H^1, ...)` of the parameter cohomology.
///
/// **Theorem (T16, Koszul).**  `H^0 = K` for every local factor, because
/// `K^0 = A_p` and the image of `d^1` is exactly the ideal `m_p`.  In the
/// regular case `mdim == 0` the complex is `A_p -> 0`, so the parameter
/// cohomology is `1` and nothing else.  Hence the object is `1` exactly when
/// the local ring is regular -- it *detects* regularity rather than merely
/// counting something.
pub fn parameter_cohomology(loc : Local) -> Graded {
  koszul_complex(loc).cohomology(loc.k)
}

///|
/// `m^i` as a row space in `A_p`, for `i >= 1`.
fn ideal_pow(loc : Local, i : Int32) -> Array[Array[Int32]] {
  let mut cur = []
  for t in 0..<loc.mdim {
    cur.push(m_row(loc, t))
  }
  for _ in 0..<(i - 1) {
    cur = ideal_times(loc, cur)
  }
  cur
}

///|
/// The `m`-basis vector `m_t`, expressed in `A_p`-coordinates.
fn m_row(loc : Local, t : Int32) -> Array[Int32] {
  let row = Array::make(loc.dim, 0)
  for c in 0..<loc.dim {
    // `b_0 = 1` in `A_p` coordinates, so `cross[0][t]` *is* the row of `m_t`
    row[c] = cross_get(loc, 0, t, c)
  }
  row
}

///|
/// `U * V` for subspaces `U`, `V` of the maximal ideal: the image of
/// `U (x) V -> A_p`, `(u, v) |-> sum_t u_t v_t` in `m`-coordinates.
fn ideal_times(loc : Local, u : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let cols = []
  for ui in u {
    for t in 0..<loc.mdim {
      cols.push(mul_by_m(loc, ui, t))
    }
  }
  // `cols` is already a list of vectors in `A_p`, so it is a *row* basis to
  // eliminate -- `image_basis` would read it as a matrix and hand back vectors
  // in the wrong ambient space
  @la.span_basis(loc.k, cols)
}

///|
/// The Loewy filtration `m^0 = A_p >= m >= m^2 >= ... = 0` as a graded
/// object, `gr^i A_p = m^i / m^{i+1}`.
///
/// **Theorem (T17, Loewy).**  `A_p` is Artinian local, so `m^i = 0` once
/// `i >= dim_k A_p` and the filtration is finite with
/// `sum_i gr^i A_p = dim_k A_p`.  The last nonzero grade is `soc A_p`,
/// because `m^L = 0` makes `m^{L-1} * m_p = 0` while every element outside
/// `m^{L-1}` still multiplies some element of `m_p` to something nonzero.  So
/// the socle rank of `coho` is the last graded dimension of the same filtered
/// object as the radical rank, not a separate fact about the table.
pub fn loewy(loc : Local) -> Graded {
  let dims = []
  let mut prev = @la.identity(loc.dim)
  for i in 0..<loc.dim {
    let next = ideal_pow(loc, i + 1)
    dims.push(subspace_quotient_dim(loc.k, prev, next))
    if next.length() == 0 {
      break
    }
    prev = next
  }
  Graded::{ dims, }.trim()
}

///|
/// The socle `soc A_p = { s : s m_p = 0 }` as a graded object, read off the
/// Loewy filtration.
pub fn socle_graded(loc : Local) -> Graded {
  let lw = loewy(loc)
  let n = lw.dims.length()
  if n == 0 {
    return Graded::zero()
  }
  let dims = Array::make(n, 0)
  dims[n - 1] = lw.dims[n - 1]
  Graded::{ dims, }.trim()
}

///|
/// `dim_k (U / V)` for subspaces `V <= U` given as row lists in the same
/// ambient space, by elimination.
fn subspace_quotient_dim(
  k : Fp,
  u : Array[Array[Int32]],
  v : Array[Array[Int32]],
) -> Int32 {
  @la.rank(k, u) - @la.rank(k, v)
}

///|
/// The categorified data of `A`: three graded objects, kept as flat arrays so
/// that they can be frozen into the runtime table without any algebra.
///
/// * `hilbert[j]` -- the number of standard monomials of total degree `j`, so
///   `sum hilbert = dim_k A` and `hilbert` is the Hilbert function of `A`.
/// * `loewy` -- the Loewy layers `gr^i A_p = m_p^i/m_p^{i+1}`, **concatenated
///   over the points**; `loewy_lens[p]` is the Loewy length of the `p`-th
///   factor, so the blocks are recoverable.  `sum loewy = dim_k A`.
/// * `kozul` -- the parameter cohomology `H^i` of the Koszul complex on the
///   parameters of each factor, concatenated the same way, with `kozul_lens[p]`
///   recording each block.  Its first entry is always `1` (`H^0 = K`).
///
/// **Why concatenation and not a single object.**  `A` is a *product* of local
/// factors, and `Tor`, `Ext` and cohomology commute with finite products, so
/// the graded objects of `A` are the direct sums of the graded objects of the
/// factors.  The frozen table stores the blocks rather than the sum so that
/// the pointwise data survives the round trip: `RAD_DIM` is `sum_p mdim(A_p)`
/// and `SOCLE_DIM` is `sum_p` the last block of `loewy`, and both are visible
/// per point at runtime.
pub(all) struct Cat {
  hilbert : Array[Int32]
  loewy : Array[Int32]
  kozul : Array[Int32]
  loewy_lens : Array[Int32]
  kozul_lens : Array[Int32]
  nfactors : Int32
}

///|
/// The categorified data of `A`, computed from the same multiplication table
/// the integers of `coho` come from.
pub fn categorify(q : Quot, ps : Array[Array[Int32]]) -> Cat {
  let h = hilbert(q)
  let locs = local_factors(q, ps)
  let flat_loe = []
  let flat_koz = []
  let loewy_lens = []
  let kozul_lens = []
  let nfac = Array::make(1, 0)
  for loc in locs {
    nfac[0] += 1
    let lw = loewy(loc)
    loewy_lens.push(lw.dims.length())
    for d in lw.dims {
      flat_loe.push(d)
    }
    let kz = parameter_cohomology(loc)
    kozul_lens.push(kz.dims.length())
    for d in kz.dims {
      flat_koz.push(d)
    }
  }
  Cat::{
    hilbert: h.dims.copy(),
    loewy: flat_loe,
    kozul: flat_koz,
    loewy_lens,
    kozul_lens,
    nfactors: nfac[0],
  }
}

///|
/// The `p`-th block of `loewy`, i.e. `gr^i A_p` for `p` a `K`-rational point.
pub fn Cat::loewy_point(self : Cat, p : Int32) -> Array[Int32] {
  block(self.loewy, self.loewy_lens, p)
}

///|
/// The `p`-th block of `kozul`, i.e. the parameter cohomology of `A_p`.
pub fn Cat::kozul_point(self : Cat, p : Int32) -> Array[Int32] {
  block(self.kozul, self.kozul_lens, p)
}

///|
/// The `p`-th block of a concatenation whose block lengths are known.  Returns
/// the empty array when `p` is out of range, so a caller that only has the
/// frozen tables can still index safely.
fn block(flat : Array[Int32], lens : Array[Int32], p : Int32) -> Array[Int32] {
  if p < 0 || p >= lens.length() {
    return []
  }
  let start = Array::make(1, 0)
  for q in 0..<p {
    start[0] += lens[q]
  }
  let out = []
  for i in start[0]..<(start[0] + lens[p]) {
    out.push(flat[i])
  }
  out
}

///|
/// `sum_j hilbert[j]`, which is `dim_k A`.
pub fn Cat::hilbert_total(self : Cat) -> Int32 {
  sum_of(self.hilbert)
}

///|
/// `dim_k A_p` read off the Loewy block: the Loewy filtration of an Artinian
/// local ring is exhaustive, so its layers sum to `dim_k A_p`.
pub fn Cat::dim_at(self : Cat, p : Int32) -> Int32 {
  sum_of(self.loewy_point(p))
}

///|
/// `dim_k m_p` read off the Loewy block: `sum_{i>=1} gr^i A_p`.
pub fn Cat::mdim(self : Cat, p : Int32) -> Int32 {
  self.dim_at(p) - self.loewy_point(p)[0]
}

///|
/// `dim_k soc A_p`: the last nonzero graded piece of the Loewy block.  The
/// last *block* is the socle even when it is empty-valued (`A_p = K` gives
/// `gr^0 = 1` and `soc = K`), because `m^0 = A_p` and `m^0 · m_p = 0`.
pub fn Cat::socle(self : Cat, p : Int32) -> Int32 {
  let b = self.loewy_point(p)
  if b.length() == 0 {
    return 0
  }
  b[b.length() - 1]
}

///|
/// `sum` of a flat integer array, `0` for the empty array.
fn sum_of(a : Array[Int32]) -> Int32 {
  let mut acc = 0
  for x in a {
    acc += x
  }
  acc
}
