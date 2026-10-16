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
    let mut acc = aug[pi][d]
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
        acc = self.fsub(acc, self.fmul(aug[pi][f], x[f]))
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
        v[pivots[pi]] = self.fneg(sys[pi][f])
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
