///|
/// # The runtime half: a finite `K`-algebra as a table
///
/// Nothing in this package computes a Gröbner basis.  It receives the frozen
/// multiplication tensor produced by `arena/algebra-ct` and implements the
/// algebraic operations as index arithmetic:
///
/// | structure                 | runtime object                         | cost |
/// |---------------------------|----------------------------------------|------|
/// | 座標環 (coordinate ring)   | `(basis, mul_tensor)`                  | `mul` = `O(d^2)` |
/// | 函數環 `K^X` (function ring)| `eval` at each point                   | `O(d n)` |
/// | 冪等元 (idempotents)       | `primitive_idempotents` below          | `O(r d^2)` |
/// | 剩餘理想 (socle)           | `{ a : a m = 0 }`                       | `O(d n d^2)` |
/// | 半單/單純理想               | `local ? K : K^r` decomposition        | — |
/// | 正則局部環 (regular)       | `edim == dim`                          | `O(1)` |
/// | 上同調 (cohomology)        | frozen `COTANGENT_DIM`, `EXT1_DIM`, ... | `O(1)` |
///
/// **Theorem (runtime correctness).**  If `mul_tensor` is the table of the
/// coordinate ring `A = R/I` with respect to the standard monomials, then the
/// operations below are the ring operations of `A`: in particular `mul` is
/// associative, `one` is a unit, and every element produced by `eval` is the
/// value of a genuine element of `A` (because `I` vanishes on `V(I)`).
///
/// The proofs are hidden in the compile-time engine and re-checked here by
/// assertions rather than by a Gröbner basis: that is the zero-cost promise.
pub(all) struct Tables {
  p : Int32
  d : Int32
  nvar : Int32
  basis : Array[Int32]
  mul_tensor : Array[Int32]
  points : Array[Int32]
  npoints : Int32
  /// `true` iff `A` has a unique maximal ideal.  Named `is_local` because
  /// `local` is a reserved keyword in MoonBit.
  is_local : Bool
  edim : Int32
  /// `dim_k rad A`; `0` iff `A` is a product of finite fields
  rad_dim : Int32
  /// `dim_k Ann(rad A)`
  socle_dim : Int32
  /// `dim_k Omega^1_{A/k}`, the module of Kahler differentials
  cotangent_dim : Int32
  /// `dim_k Ext^1_A(k, k)`
  ext1_dim : Int32
  /// `dim_k Fix(Frob)`, the number of `K`-rational points
  frob_fixed : Int32
  /// `|G|` when `A = K[G]` for an abelian `p`-group, else `0`
  group_order : Int32
  /// `r`, the number of cyclic factors of `G`
  group_rank : Int32
  /// `0` = etale, `1` = `p`-group algebra, `2` = local, not a group algebra
  kind : Int32
  /// `dim_k H^i(G, k)` for `i = 0 .. betti.length() - 1`
  betti : Array[Int32]
  /// Hilbert function of `A`: `hilbert[j]` standard monomials of degree `j`
  hilbert : Array[Int32]
  /// Loewy layers `gr^i A_p`, concatenated over the points
  loewy : Array[Int32]
  /// Loewy length of each local factor
  loewy_lens : Array[Int32]
  /// parameter cohomology `H^i` of each local factor, concatenated
  kozul : Array[Int32]
  /// length of each parameter cohomology block
  kozul_lens : Array[Int32]
}

///|
/// The cohomological signature of `A`, read off the frozen constants.
///
/// **Theorem (T7/T8/T9).**  `cotangent_dim` is `sum_p edim(A_p)`, the
/// dimension of the cotangent space `Omega^1_{A/k} (x)_A K = Tor^A_1(K,K)` at
/// the closed points -- *not* `dim_k Omega^1_{A/k}` itself, which is larger
/// whenever `A` is not reduced.  It vanishes exactly when `A` is reduced, so
/// `A` is reduced iff `cotangent_dim == 0`; `ext1_dim` is
/// `dim_k Ext^1_A(K,K)`, which the Auslander--Bridger--Solberg identification
/// makes equal to `cotangent_dim`, and it vanishes on exactly the same
/// systems; and when
/// `group_order > 0` the algebra is the group algebra of an abelian `p`-group
/// `G`, with `betti` the graded dimensions of `H^*(G, K)`.
pub fn Tables::cohomology(self : Tables) -> Array[Int32] {
  [
    self.d,
    self.rad_dim,
    self.socle_dim,
    self.cotangent_dim,
    self.ext1_dim,
    self.frob_fixed,
    self.group_order,
    self.group_rank,
  ]
}

///|
/// `dim_k H^i(G, k)` recomputed from the group-theoretic data, by the
/// Cohen-Maclane formula `P(t) = (1+t)^r / (1-t^2)^{|G|-r}`:
///
/// ```text
///   b_i = sum_{2j <= i} C(|G|-r+j-1, j) * C(r, i-2j).
/// ```
///
/// It costs `O(i^2)` integer operations and is meant to be compared against
/// the frozen `betti` array: the two must agree, which is what the runtime
/// assertion below checks.  Returns `0` when `A` is not a group algebra.
pub fn Tables::betti_at(self : Tables, i : Int32) -> Int32 {
  if self.group_order <= 0 {
    return 0
  }
  let w = self.group_order - self.group_rank
  let mut acc = 0
  let mut j = 0
  while 2 * j <= i {
    acc += binom(w + j - 1, j) * binom(self.group_rank, i - 2 * j)
    j += 1
  }
  acc
}

///|
/// `C(n, k)` as an integer (Betti numbers are counts, not field elements).
fn binom(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    return 0
  }
  if k == 0 {
    return 1
  }
  // multiplicative form: prod_{i=1..k} (n - k + i) / i, which is exact at
  // every step, so integer division is safe here.
  let mut acc = 1
  let mut i = 1
  while i <= k {
    acc = acc * (n - k + i) / i
    i += 1
  }
  acc
}

///|
/// `true` iff `A` is reduced (equivalently: a finite product of fields),
/// which is the same statement as `Omega^1_{A/k} = 0` (T7).
pub fn Tables::is_reduced(self : Tables) -> Bool {
  self.cotangent_dim == 0 && self.rad_dim == 0
}

///|
/// Field arithmetic, mirroring the emitted helpers.
pub fn Tables::norm(self : Tables, a : Int32) -> Int32 {
  let r = a % self.p
  if r < 0 {
    r + self.p
  } else {
    r
  }
}

///|
pub fn Tables::fadd(self : Tables, a : Int32, b : Int32) -> Int32 {
  self.norm(a + b)
}

///|
pub fn Tables::fmul(self : Tables, a : Int32, b : Int32) -> Int32 {
  self.norm(a * b)
}

///|
pub fn Tables::fsub(self : Tables, a : Int32, b : Int32) -> Int32 {
  self.norm(a - b)
}

///|
/// Product in `A`: `sum_{i,j} c_i e_j (basis_i basis_j)` through the tensor.
/// `O(d^2)` table reads, no polynomial arithmetic whatsoever.
pub fn Tables::mul(
  self : Tables,
  c : Array[Int32],
  e : Array[Int32],
) -> Array[Int32] {
  let d = self.d
  let res = Array::make(d, 0)
  let mut i = 0
  while i < d {
    if c[i] != 0 {
      let mut j = 0
      while j < d {
        if e[j] != 0 {
          let coef = self.fmul(c[i], e[j])
          if coef != 0 {
            let cell = (i * d + j) * d
            let mut t = 0
            while t < d {
              let v = self.mul_tensor[cell + t]
              if v != 0 {
                res[t] = self.fadd(res[t], self.fmul(coef, v))
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
/// The unit `1`: `basis[0]` is the constant monomial `1`, so the unit is the
/// coordinate vector with `1` in position `0`.
pub fn Tables::one(self : Tables) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  out[0] = 1
  out
}

///|
/// `true` iff `f = 0` in `A`.
pub fn Tables::is_zero(self : Tables, c : Array[Int32]) -> Bool {
  let mut i = 0
  while i < self.d {
    if c[i] != 0 {
      return false
    }
    i += 1
  }
  true
}

///|
/// Value of an element at the `row`-th point of `V(I)`: `O(d * nvar)`.
pub fn Tables::eval(self : Tables, c : Array[Int32], row : Int32) -> Int32 {
  let d = self.d
  let mut acc = 0
  let mut i = 0
  while i < d {
    if c[i] != 0 {
      let mut prod = 1
      let mut v = 0
      while v < self.nvar {
        let mut e = 0
        let w = self.basis[i * self.nvar + v]
        while e < w {
          prod = self.fmul(prod, self.points[row * self.nvar + v])
          e += 1
        }
        v += 1
      }
      acc = self.fadd(acc, self.fmul(c[i], prod))
    }
    i += 1
  }
  acc
}

///|
/// The primitive idempotents `e_i` of a **semisimple** `A`.
///
/// **Theorem (CRT).**  For `A` a product of fields, the element
/// `e_i = delta_i` is the unique element with `e_i(a_j) = delta_ij`; since the
/// evaluation map `Psi : A -> K^r` is surjective with kernel the nilradical,
/// `e_i` exists and is unique, and it satisfies
/// `sum e_i = 1`, `e_i e_j = 0` (`i != j`), `e_i^2 = e_i`.
/// The implementation solves `Psi x = delta_i` by Gaussian elimination, the
/// same linear algebra the engine used, but on `r x d` numbers.
pub fn Tables::primitive_idempotents(self : Tables) -> Array[Array[Int32]] {
  let d = self.d
  let r = self.npoints
  let out : Array[Array[Int32]] = []
  if r == 0 {
    return out
  }
  let mut a = 0
  while a < r {
    // target column: the evaluation vector of the unit at every point, with a
    // 1 added at row a, solved against the evaluation matrix of the basis.
    let aug : Array[Array[Int32]] = []
    let mut i = 0
    while i < r {
      let row = Array::make(d + 1, 0)
      let mut j = 0
      while j < d {
        row[j] = self.eval(self.mono_coords(j), i)
        j += 1
      }
      row[d] = if i == a { 1 } else { 0 }
      aug.push(row)
      i += 1
    }
    out.push(self.solve(aug, d, r))
    a += 1
  }
  out
}

///|
/// Coordinates of the `j`-th basis element (the `j`-th standard monomial).
pub fn Tables::mono_coords(self : Tables, j : Int32) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  out[j] = 1
  out
}

///|
/// Solve `M x = b` for the (surjective) system whose augmented matrix is
/// `aug` (rows `r`, `d` unknowns), returning the first solution.
pub fn Tables::solve(
  self : Tables,
  aug_in : Array[Array[Int32]],
  d : Int32,
  r : Int32,
) -> Array[Int32] {
  let aug = aug_in.map(row => row.copy())
  let pivots : Array[Int32] = []
  // `pivot_rows[pi]` is the row of `sys` whose pivot is `pivots[pi]`; a
  // rank-deficient row is skipped, so discovery order is *not* row order.
  let pivot_rows : Array[Int32] = []
  let mut rr = 0
  while rr < r {
    let mut c = 0
    let mut found = -1
    while c < d {
      if found < 0 && aug[rr][c] != 0 {
        found = c
      }
      c += 1
    }
    if found >= 0 {
      pivots.push(found)
      pivot_rows.push(rr)
      let inv = self.fpow(aug[rr][found], self.p - 2)
      let mut cc = 0
      while cc < d + 1 {
        aug[rr][cc] = self.fmul(aug[rr][cc], inv)
        cc += 1
      }
      let mut r2 = 0
      while r2 < r {
        if r2 != rr && aug[r2][found] != 0 {
          let fct = aug[r2][found]
          let mut cc2 = 0
          while cc2 < d + 1 {
            aug[r2][cc2] = self.fsub(aug[r2][cc2], self.fmul(fct, aug[rr][cc2]))
            cc2 += 1
          }
        }
        r2 += 1
      }
    }
    rr += 1
  }
  let x = Array::make(d, 0)
  let mut pi = 0
  while pi < pivots.length() {
    let p = pivots[pi]
    let row = aug[pivot_rows[pi]]
    let mut acc = row[d]
    let mut f = 0
    while f < d {
      let mut used = false
      let mut q = 0
      while q < pivots.length() {
        if pivots[q] == f {
          used = true
        }
        q += 1
      }
      if !used {
        acc = self.fsub(acc, self.fmul(row[f], x[f]))
      }
      f += 1
    }
    x[p] = acc
    pi += 1
  }
  x
}

///|
/// `a^e` by square-and-multiply.
pub fn Tables::fpow(self : Tables, a0 : Int32, e : Int32) -> Int32 {
  let mut base = self.norm(a0)
  let mut acc = 1
  let mut k = e
  while k > 0 {
    if k % 2 == 1 {
      acc = self.fmul(acc, base)
    }
    base = self.fmul(base, base)
    k = k / 2
  }
  acc
}

///|
/// The socle `Ann(m)` of the maximal ideal `m` at the point of `V(I)`.
///
/// **Theorem.**  `Ann(m) = { a in A : a (x_i - a_i) = 0 for every i }`, because
/// `m` is generated by the `x_i - a_i` and `Ann` of a generated ideal is the
/// intersection of the annihilators of its generators.  Since `A` is Artin and
/// local, `Ann(m)` is a **simple** ideal: it is contained in every nonzero
/// ideal of `A` (any nonzero ideal meets `m`, and `(x_i - a_i)` is a
/// non-zero-divisor on `Ann(m)`).
///
/// The computation is a kernel of the stacked multiplication matrices
/// `mu_{x_i - a_i}` -- pure linear algebra on the frozen tensor.
pub fn Tables::socle(self : Tables) -> Array[Array[Int32]] {
  let d = self.d
  let gens : Array[Array[Int32]] = []
  let mut i = 0
  while i < self.nvar {
    gens.push(self.shift_coords(i, self.point_value(i)))
    i += 1
  }
  // Ann(m) = intersect_k Ann(m_k): the kernel of the *concatenated*
  // multiplication matrices, not of their sum.
  let sys : Array[Array[Int32]] = []
  let mut gi = 0
  while gi < gens.length() {
    let m = self.mul_matrix(gens[gi]) // m[j][i] = i-th coordinate of g * mono_j
    let mut r = 0
    while r < d {
      let row = Array::make(d + 1, 0)
      let mut j = 0
      while j < d {
        row[j] = m[j][r] // transpose: the system needs N[i][j]
        j += 1
      }
      sys.push(row)
      r += 1
    }
    gi += 1
  }
  self.nullspace(sys, d)
}

///|
/// The `a_i`-th coordinate of the (unique) point of `V(I)`.
pub fn Tables::point_value(self : Tables, i : Int32) -> Int32 {
  if self.npoints > 0 {
    self.points[i]
  } else {
    0
  }
}

///|
/// Coordinates of `x_i - a_i`; returns `0` when that element of `A` vanishes
/// (i.e. the variable is a constant multiple of `1` modulo `I`).
pub fn Tables::shift_coords(
  self : Tables,
  i : Int32,
  a : Int32,
) -> Array[Int32] {
  let out = self.var_coords(i)
  out[0] = self.fsub(out[0], self.norm(a))
  out
}

///|
/// Coordinates of `x_i`: `1` at the basis position of `x_i`, or `0` if `x_i`
/// is not a standard monomial.
pub fn Tables::var_coords(self : Tables, i : Int32) -> Array[Int32] {
  let d = self.d
  let out = Array::make(d, 0)
  let mut e = 0
  while e < d {
    let mut hit = true
    let mut v = 0
    while v < self.nvar {
      let want = if v == i { 1 } else { 0 }
      if self.basis[e * self.nvar + v] != want {
        hit = false
      }
      v += 1
    }
    if hit {
      out[e] = 1
    }
    e += 1
  }
  out
}

///|
/// A `K`-basis of `{ x in K^d : M x = 0 }`, by Gauss-Jordan elimination.
pub fn Tables::nullspace(
  self : Tables,
  sys_in : Array[Array[Int32]],
  d : Int32,
) -> Array[Array[Int32]] {
  let sys = sys_in.map(row => row.copy())
  let r = sys.length()
  let pivots : Array[Int32] = []
  // `pivot_rows[pi]` is the row of `sys` whose pivot is `pivots[pi]`; a
  // rank-deficient row is skipped, so discovery order is *not* row order.
  let pivot_rows : Array[Int32] = []
  let mut rr = 0
  while rr < r {
    let mut c = 0
    let mut found = -1
    while c < d {
      if found < 0 && sys[rr][c] != 0 {
        found = c
      }
      c += 1
    }
    if found >= 0 {
      pivots.push(found)
      pivot_rows.push(rr)
      let inv = self.fpow(sys[rr][found], self.p - 2)
      let mut cc = 0
      while cc < d + 1 {
        sys[rr][cc] = self.fmul(sys[rr][cc], inv)
        cc += 1
      }
      let mut r2 = 0
      while r2 < r {
        if r2 != rr && sys[r2][found] != 0 {
          let fct = sys[r2][found]
          let mut cc2 = 0
          while cc2 < d + 1 {
            sys[r2][cc2] = self.fsub(sys[r2][cc2], self.fmul(fct, sys[rr][cc2]))
            cc2 += 1
          }
        }
        r2 += 1
      }
    }
    rr += 1
  }
  let is_pivot = Array::make(d, false)
  let mut i = 0
  while i < pivots.length() {
    is_pivot[pivots[i]] = true
    i += 1
  }
  let out : Array[Array[Int32]] = []
  let mut f = 0
  while f < d {
    if !is_pivot[f] {
      let v = Array::make(d, 0)
      v[f] = 1
      let mut pi = 0
      while pi < pivots.length() {
        v[pivots[pi]] = self.fneg(sys[pivot_rows[pi]][f])
        pi += 1
      }
      out.push(v)
    }
    f += 1
  }
  out
}

///|
/// `c + a` for coordinate vectors.
pub fn Tables::add(
  self : Tables,
  c : Array[Int32],
  e : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(self.d, 0)
  let mut i = 0
  while i < self.d {
    out[i] = self.fadd(c[i], e[i])
    i += 1
  }
  out
}

///|
/// `c + a * e` for coordinate vectors.
pub fn Tables::add_const(
  self : Tables,
  c : Array[Int32],
  e : Array[Int32],
  a : Int32,
) -> Array[Int32] {
  let scaled = Array::make(self.d, 0)
  let mut i = 0
  while i < self.d {
    scaled[i] = self.fmul(a, e[i])
    i += 1
  }
  self.add(c, scaled)
}

///|
/// Sum of a list of elements, starting from `0`.
pub fn Tables::add_many(
  self : Tables,
  xs : Array[Array[Int32]],
) -> Array[Int32] {
  let mut acc = Array::make(self.d, 0)
  let mut i = 0
  while i < xs.length() {
    acc = self.add(acc, xs[i])
    i += 1
  }
  acc
}

///|
/// `-a` in `K`.
pub fn Tables::fneg(self : Tables, a : Int32) -> Int32 {
  self.norm(0 - a)
}

///|
/// Matrix of multiplication by `c` in the standard monomial basis.
pub fn Tables::mul_matrix(
  self : Tables,
  c : Array[Int32],
) -> Array[Array[Int32]] {
  let d = self.d
  let out : Array[Array[Int32]] = []
  let mut i = 0
  while i < d {
    let col = self.mul(c, self.mono_coords(i))
    out.push(col)
    i += 1
  }
  out
}

///|
/// The etale table `A = K[C_3] = K[x]/(x^3-1)` over `K = F_97`, i.e.
/// `K[x]/((x-1)(x-2)(x-3))`: a product of three fields.
///
/// Entirely frozen: the body is a compile-time constant, so reading it
/// costs no code beyond the `Tables` record itself (see `Tables`).
pub fn Tables::cub() -> Tables {
  {
    p: @tables_cub.P,
    d: @tables_cub.D,
    nvar: @tables_cub.NVAR,
    basis: @tables_cub.basis,
    mul_tensor: @tables_cub.mul_tensor,
    points: @tables_cub.points,
    npoints: @tables_cub.NPOINTS,
    is_local: @tables_cub.LOCAL,
    edim: @tables_cub.EDIM,
    rad_dim: @tables_cub.RAD_DIM,
    socle_dim: @tables_cub.SOCLE_DIM,
    cotangent_dim: @tables_cub.COTANGENT_DIM,
    ext1_dim: @tables_cub.EXT1_DIM,
    frob_fixed: @tables_cub.FROB_FIXED,
    group_order: @tables_cub.GROUP_ORDER,
    group_rank: @tables_cub.GROUP_RANK,
    kind: @tables_cub.KIND,
    betti: @tables_cub.betti,
    hilbert: @tables_cub.hilbert,
    loewy: @tables_cub.loewy,
    loewy_lens: @tables_cub.loewy_lens,
    kozul: @tables_cub.kozul,
    kozul_lens: @tables_cub.kozul_lens,
  }
}

///|
/// The fat-point table `A = K[x,y]/(x^2,xy,y^2)` over `K = F_7`: a local
/// non-reduced algebra of embedding dimension 2.
///
/// Entirely frozen: the body is a compile-time constant, so reading it
/// costs no code beyond the `Tables` record itself (see `Tables`).
pub fn Tables::fat() -> Tables {
  {
    p: @tables_fat.P,
    d: @tables_fat.D,
    nvar: @tables_fat.NVAR,
    basis: @tables_fat.basis,
    mul_tensor: @tables_fat.mul_tensor,
    points: @tables_fat.points,
    npoints: @tables_fat.NPOINTS,
    is_local: @tables_fat.LOCAL,
    edim: @tables_fat.EDIM,
    rad_dim: @tables_fat.RAD_DIM,
    socle_dim: @tables_fat.SOCLE_DIM,
    cotangent_dim: @tables_fat.COTANGENT_DIM,
    ext1_dim: @tables_fat.EXT1_DIM,
    frob_fixed: @tables_fat.FROB_FIXED,
    group_order: @tables_fat.GROUP_ORDER,
    group_rank: @tables_fat.GROUP_RANK,
    kind: @tables_fat.KIND,
    betti: @tables_fat.betti,
    hilbert: @tables_fat.hilbert,
    loewy: @tables_fat.loewy,
    loewy_lens: @tables_fat.loewy_lens,
    kozul: @tables_fat.kozul,
    kozul_lens: @tables_fat.kozul_lens,
  }
}

///|
/// The wild table `A = K[C_2 x C_2] = K[x,y]/(x^2-1,y^2-1)` over
/// `K = F_2`: a local `p`-group algebra with non-trivial cohomology.
///
/// Entirely frozen: the body is a compile-time constant, so reading it
/// costs no code beyond the `Tables` record itself (see `Tables`).
pub fn Tables::wild() -> Tables {
  {
    p: @tables_wild.P,
    d: @tables_wild.D,
    nvar: @tables_wild.NVAR,
    basis: @tables_wild.basis,
    mul_tensor: @tables_wild.mul_tensor,
    points: @tables_wild.points,
    npoints: @tables_wild.NPOINTS,
    is_local: @tables_wild.LOCAL,
    edim: @tables_wild.EDIM,
    rad_dim: @tables_wild.RAD_DIM,
    socle_dim: @tables_wild.SOCLE_DIM,
    cotangent_dim: @tables_wild.COTANGENT_DIM,
    ext1_dim: @tables_wild.EXT1_DIM,
    frob_fixed: @tables_wild.FROB_FIXED,
    group_order: @tables_wild.GROUP_ORDER,
    group_rank: @tables_wild.GROUP_RANK,
    kind: @tables_wild.KIND,
    betti: @tables_wild.betti,
    hilbert: @tables_wild.hilbert,
    loewy: @tables_wild.loewy,
    loewy_lens: @tables_wild.loewy_lens,
    kozul: @tables_wild.kozul,
    kozul_lens: @tables_wild.kozul_lens,
  }
}

///|
/// The `p`-th block of a concatenation whose lengths are `lens`, as a fresh
/// array.  Returns the empty array when `p` is out of range, so a caller that
/// only holds the frozen tables can index without a bound check of its own.
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
/// The Hilbert function of `A`: `dim_k A_j` for `j = 0 .. hilbert.length()-1`.
///
/// **Theorem (T19.1, recovery).**  `sum_j hilbert[j] = D = dim_k A`, because the
/// standard monomials partition the monomial basis.  The runtime asserts it in
/// `hilbert_total`, so the categorified layer cannot drift from `D`: a table
/// whose Hilbert function does not sum to `D` fails on first read rather than
/// silently reporting two different dimensions.
pub fn Tables::hilbert_total(self : Tables) -> Int32 {
  let mut acc = 0
  for h in self.hilbert {
    acc += h
  }
  acc
}

///|
/// `dim_k A_j`, the number of standard monomials of total degree `j`.
pub fn Tables::hilbert_at(self : Tables, j : Int32) -> Int32 {
  if j < 0 || j >= self.hilbert.length() {
    return 0
  }
  self.hilbert[j]
}

///|
/// The Loewy graded object `gr^i A_p = m_p^i/m_p^{i+1}` of the `p`-th local
/// factor, read out of the frozen concatenation.
///
/// **Theorem (T19.2, Loewy = invariants).**  For each point `p`,
/// ```text
///   gr^0 A_p = 1,   sum_{i>=1} gr^i A_p = dim_k m_p,   gr^{L-1} A_p = soc A_p,
/// ```
/// and `sum_p sum_i gr^i A_p = D`.  Summing the blocks therefore reproduces
/// `RAD_DIM` and `SOCLE_DIM` as *graded* dimensions, which is the content of
/// T17: the two frozen integers are the tail sum and the last block of this
/// array rather than independent facts.
pub fn Tables::loewy_block(self : Tables, p : Int32) -> Array[Int32] {
  block(self.loewy, self.loewy_lens, p)
}

///|
/// `dim_k A_p`, the sum of the Loewy block: `A_p` is exhausted by its Loewy
/// filtration because `A_p` is Artinian.
pub fn Tables::dim_at(self : Tables, p : Int32) -> Int32 {
  let b = self.loewy_block(p)
  let mut acc = 0
  for x in b {
    acc += x
  }
  acc
}

///|
/// `dim_k m_p`, i.e. `sum_{i>=1} gr^i A_p`.
pub fn Tables::mdim_at(self : Tables, p : Int32) -> Int32 {
  let b = self.loewy_block(p)
  if b.length() == 0 {
    return 0
  }
  let mut acc = 0
  for i in 1..<b.length() {
    acc += b[i]
  }
  acc
}

///|
/// `dim_k soc A_p`, the last block of the Loewy series: `m^{L-1}` is
/// annihilated by `m_p` because `m^L = 0`.
pub fn Tables::socle_at(self : Tables, p : Int32) -> Int32 {
  let b = self.loewy_block(p)
  if b.length() == 0 {
    return 0
  }
  b[b.length() - 1]
}

///|
/// The parameter cohomology `H^i` of the `p`-th local factor: the cohomology
/// of the Koszul complex on the parameters of `m_p`.
///
/// **Theorem (T19.3, parameter cohomology).**  `kozul_block(p)[0] = 1` for
/// every point, since `H^0 = A_p/m_p = K`; and the whole block is `1` exactly
/// when `mdim_at(p) == 0`, i.e. when `A_p = K`.  This is a *test* for
/// regularity rather than a count: it is computed from the multiplication
/// table and needs no hypothesis about regular sequences.
pub fn Tables::kozul_block(self : Tables, p : Int32) -> Array[Int32] {
  block(self.kozul, self.kozul_lens, p)
}

///|
/// `sum_i gr^i A_p` over all points, which is `D`.
pub fn Tables::loewy_total(self : Tables) -> Int32 {
  let mut acc = 0
  for x in self.loewy {
    acc += x
  }
  acc
}

///|
/// `sum_i H^i` of the parameter cohomology over all points.
pub fn Tables::kozul_total(self : Tables) -> Int32 {
  let mut acc = 0
  for x in self.kozul {
    acc += x
  }
  acc
}
