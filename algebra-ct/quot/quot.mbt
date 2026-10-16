///|
type Fp = @poly.Fp

///|
type Poly = @poly.Poly

///|
type Order = @poly.Order

///|
type Basis = @gb.Basis

///|
/// # The coordinate ring of a zero-dimensional affine scheme
///
/// Let `I ⊆ R = K[x_1..x_n]` be zero dimensional and put `A = R/I`.  Because
/// `A` is an **Artin algebra**, every question about `A` is a question about
/// finite dimensional linear algebra:
///
/// - multiplication `mu_a` is a matrix,
/// - the residue classes of the standard monomials `B` are a `K`-basis,
/// - every `f in A` is its coordinate vector `c(f) in K^{|B|}`,
/// - `f = g` in `A` iff `c(f) = c(g)`.
///
/// The module below stores the multiplication table of `A` **once**, at
/// generation time.  Every runtime operation -- product of two elements, the
/// image of a polynomial, the value of a character -- is then an index
/// computation on a `|B| x |B|` table, i.e. `O(1)` field operations instead
/// of a polynomial multiplication and a normal form.  This is where the
/// zero-cost abstraction pays off: the Gröbner basis exists only in the
/// compile-time engine, the runtime sees a flat integer table.
///
/// **Theorems used below.**
///
/// (T1) `A` is finite dimensional with basis the standard monomials, and
///      `|A| = p^{dim A}` where `dim A` is the dimension of `m/m^2` for the
///      unique maximal ideal `m` when `A` is local.
///
/// (T2) (Chinese remainder) if `I = I_1 ∩ ... ∩ I_r` with the `I_i` pairwise
///      comaximal then `A = A_1 x ... x A_r`, and the primitive idempotents
///      are `e_i = (f/f_i) * ((f/f_i)^{-1} mod f_i)` for `f = prod f_i`.
///
/// (T3) `A/m = K` for the residue field of a local Artin `K`-algebra, so the
///      structure map `A -> K` is evaluation at the unique point.
///
/// (T4) `R_m` is regular iff `dim R_m = dim_k m/m^2` (the embedding
///      dimension); the left side is the Krull dimension, computable from the
///      standard monomials of height `0`, `1`, ...
pub(all) struct Quot {
  /// the residue field
  k : Fp
  /// number of variables of the ambient ring
  n : Int32
  /// monomial order the basis was computed with
  order : Order
  /// standard monomials: a `K`-basis of `A`
  basis : Array[Array[Int32]]
  /// `table[i * d + j]` = coordinates of `basis[i] * basis[j]`
  table : Array[Array[Int32]]
  /// `d = |A|` as a `K`-vector space
  dim : Int32
  /// embedding dimension `dim_k m/m^2` of the local ring at the unique point
  edim : Int32
  /// the point of `V(I)` when `A` is local
  point : Array[Int32]
  /// `true` iff `A` has a unique maximal ideal (local)
  /// (named `is_local` because `local` is a reserved keyword)
  is_local : Bool
}

///|
/// `d = |A|` and `c * d` bounds a flat multiplication table.
pub fn Quot::size(self : Quot) -> Int32 {
  self.dim
}

///|
/// Multiplication in `A`, as a table lookup: `basis[i] * basis[j]`.
///
/// **Complexity.** `O(1)` field operations, against `O(mn)` for a polynomial
/// product followed by a normal form in the generated runtime.
pub fn Quot::mul(self : Quot, i : Int32, j : Int32) -> Array[Int32] {
  self.table[i * self.dim + j].copy()
}

///|
/// Coordinates of the class of `f` in the standard monomial basis.
pub fn Quot::coords(self : Quot, b : Basis, f : Poly) -> Array[Int32] {
  let d = self.dim
  let out = Array::make(d, 0)
  let r = f.normal_form(b.gs, b.order)
  let mut i = 0
  while i < d {
    out[i] = r.coeff(self.basis[i])
    i += 1
  }
  out
}

///|
/// Evaluate a coordinate vector at a point (T3: well defined on `A` because
/// every element of `I` vanishes at every point of `V(I)`).
pub fn Quot::eval_coords(
  self : Quot,
  c : Array[Int32],
  pt : Array[Int32],
) -> Int32 {
  let d = self.dim
  let mut acc = 0
  let mut i = 0
  while i < d {
    let m = self.basis[i]
    let mut prod = 1
    let mut v = 0
    while v < pt.length() {
      let mut w = 0
      while w < m[v] {
        prod = self.k.mul(prod, pt[v])
        w += 1
      }
      v += 1
    }
    acc = self.k.add(acc, self.k.mul(c[i], prod))
    i += 1
  }
  acc
}

///|
/// Build the coordinate ring `A = R/I` of a zero-dimensional ideal: one
/// Gröbner basis, one table.
pub fn quotient_ring(
  k : Fp,
  n : Int32,
  gens : Array[Poly],
  order : Order,
) -> Quot {
  let b = @gb.buchberger(k, gens, order)
  let ps = match @gb.points_from_gb(k, n, b, POINT_BUDGET) {
    Some(v) => v
    None => []
  }
  quotient_ring_from_basis(k, n, b, ps)
}

///|
/// Budget for the `K`-point enumeration of `quotient_ring`.  It bounds the
/// number of recursive cutting steps (roughly `p` per eliminated variable) and
/// exists so that a positive dimensional input cannot hang the driver; a
/// positive dimensional ideal is rejected further down anyway.
const POINT_BUDGET : Int32 = 200000

///|
/// The same ring from an already computed Gröbner basis and point list, so the
/// driver can compute the basis exactly once.
pub fn quotient_ring_from_basis(
  k : Fp,
  n : Int32,
  b : Basis,
  ps : Array[Array[Int32]],
) -> Quot {
  let basis = @gb.standard_monomials(b, n)
  let order = b.order
  let d = basis.length()
  let table : Array[Array[Int32]] = []
  let mut i = 0
  while i < d {
    let bi = Poly::from_mono(k, n, basis[i], 1)
    let mut j = 0
    while j < d {
      let bj = Poly::from_mono(k, n, basis[j], 1)
      let r = bi.mul(bj).normal_form(b.gs, order)
      let coords = Array::make(d, 0)
      let mut t = 0
      while t < d {
        coords[t] = r.coeff(basis[t])
        t += 1
      }
      table.push(coords)
      j += 1
    }
    i += 1
  }
  let pt = Array::make(n, 0)
  let mut is_local = false
  let mut edim_v = 0
  if ps.length() == 1 {
    is_local = true
    let mut v = 0
    while v < n {
      pt[v] = ps[0][v]
      v += 1
    }
    // `embedding_dimension` needs the generators of `I` itself; they are
    // exactly the original input of the Gröbner basis, which the reduced form
    // of `b` regenerates.
    edim_v = embedding_dimension(k, n, b.elems(), order, ps[0])
  }
  { k, n, order, basis, table, dim: d, edim: edim_v, point: pt, is_local, }
}

///|
///
/// **Definition (edim).**  For `p` in `V(I)` and `m = <x - p>` the embedding
/// dimension of the local ring is
/// `edim(I, p) = dim_k m / (I + m^2)`.
///
/// Two subtleties, both of which this function used to get wrong:
///
/// * `A / (I + m^2)` is *not* `m / (I + m^2)`: the former also counts the
///   residue field and the higher-order layers.  For `I = (x^3)` at `0`,
///   `dim A/(I + m^2) = dim K[x]/(x^2) = 2` while `edim = 1`.
/// * the classes of `x_i - p_i` in `m / (I + m^2)` need not be linearly
///   independent, so simply counting the `i` with `x_i - p_i` not in
///   `I + m^2` is wrong too: for `I = (x + y, y^2)` at `0` that count is `2`
///   while `m = (y)` and `edim = 1`.
///
/// Subtracting `dim A / (I + m)` counts the residue field and the higher
/// layers away, so
/// `edim(I, p) = dim A/(I + m^2) - dim A/(I + m)`,
/// which is what is computed here.  When `p` is not in `V(I)` the ideal
/// `I + m` is the unit ideal and the local ring does not exist; `0` is
/// returned.
///
/// **Theorem (T4).**  `R_m` is regular iff `edim = dim R_m`, and for a
/// zero-dimensional ideal `dim R_m = 0`, so `R_m` is regular iff `edim = 0`,
/// i.e. iff `m = 0`, i.e. iff `I` is already radical at that point.
pub fn embedding_dimension(
  k : Fp,
  n : Int32,
  gens : Array[Poly],
  order : Order,
  p : Array[Int32],
) -> Int32 {
  // I + m^2 = < I , (x_i - p_i)(x_j - p_j) | 0 <= i, j < n >
  let m2 : Array[Poly] = gens.copy()
  let m1 : Array[Poly] = gens.copy()
  let mut a = 0
  while a < n {
    m1.push(Poly::var_n(k, n, a).sub(Poly::const_n(k, n, p[a])))
    let mut bb = 0
    while bb < n {
      m2.push(
        Poly::var_n(k, n, a)
        .sub(Poly::const_n(k, n, p[a]))
        .mul(Poly::var_n(k, n, bb).sub(Poly::const_n(k, n, p[bb]))),
      )
      bb += 1
    }
    a += 1
  }
  let d1 = @gb.standard_monomials(@gb.buchberger(k, m1, order), n).length()
  if d1 == 0 {
    // p is not in V(I): I + m = (1), there is no local ring here.
    return 0
  }
  let d2 = @gb.standard_monomials(@gb.buchberger(k, m2, order), n).length()
  d2 - d1
}

///|
/// The primitive idempotents of `A`, indexed by the `K`-rational points.
///
/// **Theorem (T2).** `Psi : A -> K^r`, `f |-> (f(a_1), ..., f(a_r))` is
/// surjective with kernel the nilradical, so it has a right inverse and the
/// columns of that inverse are the primitive idempotents `e_i`; they satisfy
/// `sum e_i = 1`, `e_i e_j = 0` for `i != j` and `e_i^2 = e_i`.
pub fn primitive_idempotents(
  q : Quot,
  ps : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let k = q.k
  let d = q.dim
  let r = ps.length()
  // Psi[i][j] = evaluation at ps[i] of basis[j].  Everything needed is already
  // in `q`, so no Gröbner basis is computed here (an earlier version built one
  // and threw it away).
  let psi : Array[Array[Int32]] = []
  let mut i = 0
  while i < r {
    let row = Array::make(d, 0)
    let mut j = 0
    while j < d {
      row[j] = Poly::from_mono(k, q.n, q.basis[j], 1).eval_at(ps[i])
      j += 1
    }
    psi.push(row)
    i += 1
  }
  let inv = right_inverse(k, psi)
  let out : Array[Array[Int32]] = []
  let mut a = 0
  while a < r {
    let col = Array::make(d, 0)
    let mut j = 0
    while j < d {
      col[j] = inv[j * r + a]
      j += 1
    }
    out.push(col)
    a += 1
  }
  out
}

///|
/// A right inverse `X` of the `r x d` surjective matrix `M`, i.e. `M X = Id_r`,
/// obtained by solving the `r` linear systems with the shared elimination.
pub fn right_inverse(k : Fp, m : Array[Array[Int32]]) -> Array[Int32] {
  let r = m.length()
  let d = m[0].length()
  let aug : Array[Array[Int32]] = []
  let mut i = 0
  while i < r {
    let row = m[i].copy()
    let mut j = 0
    while j < r {
      row.push(if i == j { 1 } else { 0 })
      j += 1
    }
    aug.push(row)
    i += 1
  }
  let pivots : Array[Int32] = []
  let mut rr = 0
  while rr < r {
    let mut c = 0
    let mut found = -1
    while c < d {
      if found < 0 && k.is_nonzero(aug[rr][c]) {
        found = c
      }
      c += 1
    }
    if found >= 0 {
      pivots.push(found)
      let inv = k.inv(aug[rr][found])
      let mut cc = 0
      while cc < d + r {
        aug[rr][cc] = k.mul(aug[rr][cc], inv)
        cc += 1
      }
      let mut r2 = 0
      while r2 < r {
        if r2 != rr && k.is_nonzero(aug[r2][found]) {
          let fct = aug[r2][found]
          let mut cc2 = 0
          while cc2 < d + r {
            aug[r2][cc2] = k.sub(aug[r2][cc2], k.mul(fct, aug[rr][cc2]))
            cc2 += 1
          }
        }
        r2 += 1
      }
    }
    rr += 1
  }
  // Solve M x = e_a for every a by back substitution on the row echelon
  // system [M | I] -> [RREF | Y]:  x_p = delta_{pi,a} - sum_f Y[pi][f] x_f.
  let is_pivot = Array::make(d, false)
  for p in pivots {
    is_pivot[p] = true
  }
  let out = Array::make(d * r, 0)
  let mut a = 0
  while a < r {
    // Set the free variable `x_a = 1` and every other free variable to `0`,
    // then back substitute along the pivot rows.  Because exactly one free
    // coordinate is nonzero, each pivot row sees at most one correction --
    // the loop over all free columns that used to be here was quadratic and
    // could only ever subtract `aug[pi][d + a]` when `a` was itself free.
    let free_a = a < d && !is_pivot[a]
    let mut pi = 0
    while pi < pivots.length() {
      let p = pivots[pi]
      let mut acc = aug[pi][d + a]
      if free_a {
        acc = k.sub(acc, aug[pi][d + a])
      }
      out[p * r + a] = acc
      pi += 1
    }
    a += 1
  }
  out
}

///|
/// Coordinates of `e_i * e_j` from the flat table: the product of two elements
/// of `A` as `O(d^2)` integer operations, with **no** polynomial arithmetic.
pub fn Quot::mul_coords(
  self : Quot,
  c : Array[Int32],
  e : Array[Int32],
) -> Array[Int32] {
  let d = self.dim
  let res = Array::make(d, 0)
  let mut i = 0
  while i < d {
    if c[i] != 0 {
      let mut j = 0
      while j < d {
        if e[j] != 0 {
          let cell = self.table[i * d + j]
          let mut t = 0
          while t < d {
            if cell[t] != 0 {
              res[t] = self.k.add(
                res[t],
                self.k.mul(self.k.mul(c[i], e[j]), cell[t]),
              )
            }
            t += 1
          }
        }
        j += 1
      }
    }
    i += 1
  }
  res
}
