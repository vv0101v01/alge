///|
/// # Cohomology and isomorphism invariants of an Artin `K`-algebra
/// |
/// This package is the derived layer of the engine: given the finite
/// `K`-algebra `A = R/I` (`R = K[x_1..x_n]`), it computes the invariants that
/// classify it up to `K`-algebra isomorphism, together with the first two
/// cohomological quantities that those invariants encode.
///
/// **What is computed.**
/// | Invariant | Meaning | Formula |
/// |---|---|---|
/// | `rad_dim` | `dim_k rad A` | kernel of the stacked point evaluations |
/// | `socle_dim` | `dim_k Ann(rad A)` | kernel of the stacked multiplication matrices |
/// | `cotangent_dim` | `dim_k (Omega^1_{A/k} (x)_A K) = dim_k Tor^A_1(K,K)` | `sum_p edim(A_p)` |
/// | `ext1_dim` | `dim_k Ext^1_A(k,k)` | `sum_p (n - rank(grad I | p))` |
/// | `frob_fixed` | `dim_k Fix(Frob)` | number of `K`-rational points |
/// | `group_order`, `group_rank` | `|G|`, `r` | only when `A = k[G]`, `G` a `p`-group |
/// | `betti` | `dim_k H^i(G,k)` | Cohen-Maclane Poincare series |
///
/// **Theorems proved here (all verified by the assertions in
/// `coho_wbtest.mbt`).**
///
/// *T7 (differentials vs embedding dimension).*  For an Artin local
/// `K`-algebra with residue `k = K`,
/// `Omega^1_{A/k} = m/m^2`, hence `dim_k Omega^1_{A/k} = edim(A)`; for a
/// split product `A = prod A_i`,
/// `Omega^1_{A/k} = prod Omega^1_{A_i/k}` and `dim_k Omega^1_{A/k} =
/// sum_p edim(A_p)` (summed over the closed points).  In particular
/// `Omega^1_{A/k} = 0  <=>  A is reduced  <=>  edim = 0 everywhere`.
///
/// *T8 (first cohomology of the simple module).*  The cotangent complex of
/// `k = A/m` gives
/// ```text
///   Ext^1_A(k, k) = coker( I/mI -> Omega^1_{R/k} tensor k ),
/// ```
/// and `I/(I^2 + mI) = I/mI` is spanned by the images of *any* generating
/// set of `I`, so with `f_1..f_s` generating `I`
/// `Ext^1_A(k,k) = k^n / < (d f_i / dx_v)_v >`.  In particular `Ext^1 = 0`
/// iff the Jacobian of `I` at `m` has full rank `n`, which for a
/// hypersurface is the classical `A/(f') = 0`, i.e. `gcd(f, f') = 1`, i.e.
/// `A` reduced.  For the two tables: cub `Ext^1 = 0` (reduced), fat
/// `Ext^1 = k^2` (all partial derivatives vanish modulo `m`).
///
/// *T9 (signature of a group algebra).*  If `G = prod C_{p^{lambda_i}}` with
/// `r` factors then
/// ```text
///   k[G] = k[x_1..x_r] / (x_i^{p^{lambda_i}}),   |G| = p^r,
///   edim(k[G]) = r,        soc(k[G]) = A * N,  N = sum_{g in G} g,
///   dim_k soc(k[G]) = 1.
/// ```
/// (`soc A = Ann(A^p A)` for a group algebra and `soc = A * N`; `N != 0`
/// because the algebra of a `p`-group over `k = F_p` is local.)  Hence
/// `(dim_k A, edim(A), dim_k soc(A)) = (p^r, r, 1)` is the signature of a
/// `p`-group algebra and those three numbers force the number `r` of cyclic
/// factors.  Note that `dim soc` alone does **not** see `r`: `soc(k[G])` is
/// one-dimensional for every `G`.
///
/// *T10 (Cohen-Maclane).*  For `G` a finite abelian `p`-group and `k = F_p`,
/// `H^*(G,k) = Lambda^*(V) tensor k[W]` with `dim V = r` (degree `1`) and
/// `dim W = |G| - r` (degree `2`), so the graded ring -- hence its whole
/// Poincare series
/// ```text
///   P_G(t) = (1+t)^r / (1-t^2)^{|G|-r}
/// ```
/// -- is a function of `(|G|, r)` alone.  Conversely, if `|G|` is coprime to
/// `p` (Maschke) then `H^i(G,k) = 0` for `i > 0`, which is why the "etale"
/// table has no positive-degree cohomology at all.
///
/// *T11 (Frobenius data).*  For `K = F_p` the Frobenius `F(a) = a^p` is a
/// `K`-linear automorphism of `A`, `dim_k Fix(F) = #K-points`, and the
/// multiset of residue-field degrees is recovered from
/// `dim Fix(F^{p^i}) - dim Fix(F^{p^{i-1}})`; `Omega^1 = 0` iff all of them
/// are `1`.
///
type Fp = @poly.Fp

///|
type Poly = @poly.Poly

///|
type Quot = @quot.Quot

///|
type Order = @poly.Order

///|
/// The isomorphism invariants of one Artin algebra.  Every field is an
/// integer that the runtime can compare against a frozen constant, which is
/// the whole point: the cohomological structure of `A` is frozen into
/// integers at compile time and costs nothing at runtime.
pub(all) struct Inv {
  /// `dim_k A`
  dim : Int32
  /// number of variables of the ambient polynomial ring
  nvar : Int32
  /// `dim_k rad A` (`0` iff `A` is a product of fields)
  rad_dim : Int32
  /// `dim_k Ann(rad A)`
  socle_dim : Int32
  /// `dim_k (Omega^1_{A/k} (x)_A K) = dim_k Tor^A_1(K,K) = sum_p edim(A_p)`.
  ///
  /// NOT `dim_k Omega^1_{A/k}` itself, which is larger whenever `A` is not
  /// reduced: for `A = K[x,y]/(x^2,xy,y^2)` one has `dim_k Omega^1 = 3` but
  /// `dim_k (Omega^1 (x)_A K) = 2`.  Tensors commute with the finite sum over
  /// the local factors, so the number computed here is the cotangent space of
  /// the closed points, which is what a moduli problem actually sees.
  cotangent_dim : Int32
  /// `dim_k Ext^1_A(K,K) = dim_k Tor^A_1(K,K) = cotangent_dim` (the Auslander
  /// --Bridger--Solberg identification for an Artin algebra with residue field
  /// `K`), computed independently as the pointwise cokernel of the Jacobian.
  ext1_dim : Int32
  /// `dim_k Fix(Frob)` = number of `K`-rational points of `V(I)`
  frob_fixed : Int32
  /// `|G|` when `A = k[G]` for an abelian `p`-group, else `0`
  group_order : Int32
  /// `r`, the number of cyclic factors of `G`, else `0`
  group_rank : Int32
  /// `dim_k H^i(G,k)` for `i = 0 .. betti.length() - 1`
  betti : Array[Int32]
}

///|
/// Classification of an Artin algebra by the invariants of T9/T11.
/// `0` = etale (a product of finite fields), `1` = a `p`-group algebra
/// (local, non-reduced), `2` = a local algebra that is neither.
pub(all) struct Kind {
  code : Int32
  name : String
}

///|
pub fn Inv::kind(self : Inv) -> Kind {
  kind_of(self)
}

///|
pub fn kind_of(inv : Inv) -> Kind {
  if inv.rad_dim == 0 {
    { code: 0, name: "etale", }
  } else if inv.group_order > 0 {
    { code: 1, name: "p-group-algebra", }
  } else {
    { code: 2, name: "local-non-group", }
  }
}

///|
/// All the invariants of `A`, computed from the frozen multiplication table
/// and the Gröbner basis.
///
/// **Precondition.**  `A` is split over `K` (`rad A` is the ideal of the
/// elements vanishing at every `K`-rational point).  Every table in
/// `spec/spec.txt` satisfies this; a non-split ideal would need the closed
/// points over an algebraic closure.
pub fn analyse(
  k : Fp,
  n : Int32,
  gens : Array[Poly],
  order : Order,
  q : Quot,
  ps : Array[Array[Int32]],
) -> Inv {
  let d = q.dim
  let rad = radical_basis(q, ps)
  let soc = socle_basis(q, rad)
  let mut cotangent = 0
  let mut ext1 = 0
  let mut row = 0
  while row < ps.length() {
    cotangent += @quot.embedding_dimension(k, n, gens, order, ps[row])
    ext1 += ext1_at(k, n, gens, ps[row])
    row += 1
  }
  let frob = frobenius_fixed(q, 1)
  // T9: `A = k[G]` for an abelian p-group only if `dim = p^r`, and then the
  // number of cyclic factors is `r = log_p dim`, which must agree with both
  // the embedding dimension and the socle dimension.
  let mut group_order = 0
  let mut group_rank = 0
  let mut betti : Array[Int32] = []
  match log_p(d, k.p) {
    Some(r) =>
      if cotangent == r && soc.length() == 1 {
        group_order = d
        group_rank = r
        betti = cohen_maclane(d, r, 6)
      }
    None => ()
  }
  {
    dim: d,
    nvar: n,
    rad_dim: rad.length(),
    socle_dim: soc.length(),
    cotangent_dim: cotangent,
    ext1_dim: ext1,
    frob_fixed: frob,
    group_order,
    group_rank,
    betti,
  }
}

///|
/// `rad A` as a `K`-basis: the elements of `A` that vanish at every closed
/// point.  For a split algebra this is exactly the Jacobson radical, whose
/// vanishing set is `V(A)`.
fn radical_basis(q : Quot, ps : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let d = q.dim
  let rows : Array[Array[Int32]] = []
  let mut r = 0
  while r < ps.length() {
    let row = Array::make(d, 0)
    let mut i = 0
    while i < d {
      let mut prod = 1
      let mut v = 0
      while v < q.n {
        let pt = ps[r][v]
        let mut e = 0
        while e < q.basis[i][v] {
          prod = q.k.mul(prod, pt)
          e += 1
        }
        v += 1
      }
      row[i] = prod
      i += 1
    }
    rows.push(row)
    r += 1
  }
  @gb.nullspace(q.k, rows, d)
}

///|
/// `soc A = Ann(rad A)` as a `K`-basis: the kernel of the stacked
/// multiplication matrices `mu_r` for a basis of `rad A`.
fn socle_basis(q : Quot, rad : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let d = q.dim
  if rad.length() == 0 {
    // rad A = 0 means A is a product of fields: the socle is all of A, whose
    // basis is the standard monomial basis itself.
    let units : Array[Array[Int32]] = []
    let mut i = 0
    while i < d {
      let u = Array::make(d, 0)
      u[i] = 1
      units.push(u)
      i += 1
    }
    return units
  }
  // `Ann(g) = ker(mu_g)`: `mu_g` acts on the coordinates of `a`, so the system
  // is the multiplication matrix itself -- one row per *coordinate* of the
  // product, with one entry per basis element of `a`.
  let sys : Array[Array[Int32]] = []
  let mut ri = 0
  while ri < rad.length() {
    let m = mul_matrix(q, rad[ri])
    let mut j = 0
    while j < d {
      sys.push(m[j].copy())
      j += 1
    }
    ri += 1
  }
  @gb.nullspace(q.k, sys, d)
}

///|
/// `mu_g`, the matrix of multiplication by `g` in the standard monomial
/// basis: `m[j][i]` = the `j`-th coordinate of `g * basis_i`.
fn mul_matrix(q : Quot, g : Array[Int32]) -> Array[Array[Int32]] {
  let d = q.dim
  let m : Array[Array[Int32]] = []
  let mut j = 0
  while j < d {
    m.push(Array::make(d, 0))
    j += 1
  }
  let mut i = 0
  while i < d {
    let e = Array::make(d, 0)
    e[i] = 1
    let ge = mul_coords(q, g, e)
    let mut t = 0
    while t < d {
      m[t][i] = ge[t]
      t += 1
    }
    i += 1
  }
  m
}

///|
/// Coordinates of `u * v` in the standard monomial basis, from the frozen
/// tensor.
pub fn mul_coords(q : Quot, u : Array[Int32], v : Array[Int32]) -> Array[Int32] {
  let d = q.dim
  let res = Array::make(d, 0)
  let mut i = 0
  while i < d {
    if u[i] != 0 {
      let mut j = 0
      while j < d {
        if v[j] != 0 {
          let coef = q.k.mul(u[i], v[j])
          if coef != 0 {
            let cell = i * d + j
            let mut t = 0
            while t < d {
              let w = q.table[cell][t]
              if w != 0 {
                res[t] = q.k.add(res[t], q.k.mul(coef, w))
              }
              t += 1
            }
          }
        }
        j += 1
      }
    }
    i += 1
  }
  res
}

///|
/// `dim_k Ext^1_{A_p}(k, k) = n - rank(grad I | p)` -- the codimension of the
/// Jacobian of `I` inside `k^n` (T8).
fn ext1_at(k : Fp, n : Int32, gens : Array[Poly], pt : Array[Int32]) -> Int32 {
  // rows of the Jacobian evaluated at the point: `row[v][i]` = (df_i/dx_v)(pt)
  let rows : Array[Array[Int32]] = []
  let mut v = 0
  while v < n {
    let row = Array::make(gens.length(), 0)
    for i in 0..<gens.length() {
      row[i] = k.norm(gens[i].derivative(v).eval_at(pt))
    }
    rows.push(row)
    v += 1
  }
  n - rank_of(k, rows)
}

///|
/// Rank of a row echelon form computation over `K`.
fn rank_of(k : Fp, m : Array[Array[Int32]]) -> Int32 {
  let rows = m.length()
  if rows == 0 {
    return 0
  }
  let cols = m[0].length()
  let a : Array[Array[Int32]] = []
  let mut ri = 0
  while ri < rows {
    a.push(m[ri].copy())
    ri += 1
  }
  let mut rank = 0
  let mut r = 0
  while r < rows && rank < cols {
    // pivot search
    let mut piv = -1
    let mut rr = r
    while rr < rows {
      if a[rr][rank] != 0 {
        piv = rr
        break
      }
      rr += 1
    }
    if piv < 0 {
      rank += 1
      continue
    }
    let tmp = a[r]
    a[r] = a[piv]
    a[piv] = tmp
    let inv = k.inv(a[r][rank])
    let mut c = rank
    while c < cols {
      a[r][c] = k.mul(a[r][c], inv)
      c += 1
    }
    let mut rr = 0
    while rr < rows {
      if rr != r && a[rr][rank] != 0 {
        let f = a[rr][rank]
        let mut c = rank
        while c < cols {
          a[rr][c] = k.sub(a[rr][c], k.mul(f, a[r][c]))
          c += 1
        }
      }
      rr += 1
    }
    r += 1
  }
  r
}

///|
/// The Frobenius matrix `F(a) = a^p` of `A` in the standard monomial basis:
/// `F(e_i) = e_i^p`, which is `p` table multiplications.
fn frobenius_matrix(q : Quot) -> Array[Array[Int32]] {
  let d = q.dim
  // Columns first: `cols[j]` = F(e_j).
  let cols : Array[Array[Int32]] = []
  let mut j = 0
  while j < d {
    let e = Array::make(d, 0)
    e[j] = 1
    let mut acc = e
    let mut step = 1
    while step < q.k.p {
      acc = mul_coords(q, acc, e)
      step += 1
    }
    cols.push(acc)
    j += 1
  }
  // Transpose into row-major form so that `mat_mul` composes them.
  let f : Array[Array[Int32]] = []
  let mut i = 0
  while i < d {
    let row = Array::make(d, 0)
    let mut c = 0
    while c < d {
      row[c] = cols[c][i]
      c += 1
    }
    f.push(row)
    i += 1
  }
  f
}

///|
/// `dim_k Fix(F^m)` where `F` is the Frobenius of `A` (T11).  `m = 1` gives the
/// number of `K`-rational points.
pub fn frobenius_fixed(q : Quot, m : Int32) -> Int32 {
  let d = q.dim
  let f = frobenius_matrix(q)
  // F^m as a matrix, then dim of its `1`-eigenspace = rank(F^m - 1).
  let mut cur = identity(d)
  let mut step = 0
  while step < m {
    cur = mat_mul(q.k, cur, f)
    step += 1
  }
  let diff : Array[Array[Int32]] = []
  let mut i = 0
  while i < d {
    let row = Array::make(d, 0)
    let mut j = 0
    while j < d {
      row[j] = q.k.sub(cur[i][j], if i == j { 1 } else { 0 })
      j += 1
    }
    diff.push(row)
    i += 1
  }
  d - rank_of(q.k, diff)
}

///|
fn identity(d : Int32) -> Array[Array[Int32]] {
  let m : Array[Array[Int32]] = []
  let mut i = 0
  while i < d {
    let row = Array::make(d, 0)
    row[i] = 1
    m.push(row)
    i += 1
  }
  m
}

///|
fn mat_mul(
  k : Fp,
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let d = a.length()
  let out : Array[Array[Int32]] = []
  let mut i = 0
  while i < d {
    let row = Array::make(d, 0)
    let mut j = 0
    while j < d {
      let mut acc = 0
      let mut t = 0
      while t < d {
        if a[i][t] != 0 && b[t][j] != 0 {
          acc = k.add(acc, k.mul(a[i][t], b[t][j]))
        }
        t += 1
      }
      row[j] = acc
      j += 1
    }
    out.push(row)
    i += 1
  }
  out
}

///|
/// `log_p v`, or `None` when `v` is not a power of `p`.
pub fn log_p(v : Int32, p : Int32) -> Int32? {
  if v <= 0 {
    return None
  }
  let mut acc = 1
  let mut e = 0
  while acc < v {
    acc = acc * p
    e += 1
    if e > 64 {
      return None
    }
  }
  if acc == v {
    Some(e)
  } else {
    None
  }
}

///|
/// **Theorem (T10, Cohen-Maclane).**  `H^*(G,k) = Lambda^*(V) tensor k[W]`
/// with `dim V = r` in degree `1` and `dim W = |G| - r` in degree `2`, so the
/// `i`-th Betti number is the coefficient of
/// `(1+t)^r / (1-t^2)^{|G|-r}`.
///
/// The coefficients are computed as integers, using
/// `1/(1-t^2)^{w} = sum_j C(w+j-1, j) t^{2j}` together with
/// `(1+t)^r = sum_a C(r,a) t^a`, hence
/// `b_i = sum_{2j <= i} C(w+j-1, j) * C(r, i-2j)` with `w = |G| - r`.
///
/// Sanity check at `r = 2, |G| = 4` (so `w = 2`): `P = 1/(1-t)` and the
/// Betti numbers are `b_i = i+1`, the classical answer for `(Z/2)^2`.
pub fn cohen_maclane(
  group_order : Int32,
  r : Int32,
  maxdeg : Int32,
) -> Array[Int32] {
  let w = group_order - r
  let out = Array::make(maxdeg + 1, 0)
  let mut i = 0
  while i <= maxdeg {
    let mut acc = 0
    let mut j = 0
    while 2 * j <= i {
      acc += binom(w + j - 1, j) * binom(r, i - 2 * j)
      j += 1
    }
    out[i] = acc
    i += 1
  }
  out
}

///|
/// `C(n, k)` as an integer (the Betti numbers are counts, not field
/// elements, so this is ordinary integer arithmetic).
fn binom(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    return 0
  }
  let mut acc : Int64 = 1
  let mut i = 0
  while i < k {
    acc = acc * (n - i).to_int64() / (i + 1).to_int64()
    i += 1
  }
  acc.to_int()
}
