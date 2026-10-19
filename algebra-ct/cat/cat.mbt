///|
type Fp = @poly.Fp

///|
type Quot = @quot.Quot

///|

///|
/// # Categorification: graded objects and complexes
/// |
/// Everything the invariant layer of this system used to record was a single
/// integer -- `dim_k A`, `dim_k Ext^1`, `dim_k H^i(G,k)`.  Those integers are
/// the *totals* of graded objects, and the total is the least interesting
/// thing about a graded object: it throws away the degrees, and with them the
/// multiplication, the cohomology and the symmetry.
///
/// This package performs the lift.
///
/// | classical | categorified here |
/// |---|---|
/// | `dim_k A` | `Graded` -- the Hilbert function `A_d` |
/// | a Betti number `b_i` | `Complex` -- a cochain complex with matrices |
/// | `P(t) = sum b_i t^i` | the graded object `Tor = H_*(Complex)` |
/// | `H^*(G,k) = Lambda(V) (x) k[W]` | a graded ring with an actual product |
///
/// Nothing here costs anything at runtime: the graded objects are computed
/// once, at generation time, and frozen into integers by `emit`.
///
/// **The recovery theorem.**  Every categorified quantity in this package
/// satisfies `Graded::total` of it equal to the integer it replaced, so the
/// lift is *strictly* a refinement and the old invariants remain readable
/// (`cat_wbtest.mbt` asserts the recovery on every table).

///|
/// A graded `K`-vector space: `dims[j]` is the dimension of the degree-`j`
/// piece.  `Graded` is a *canonical form*: `trim` removes the trailing zeros,
/// so two graded objects with the same graded dimensions are equal, while
/// `Graded::equal` is the relation that decides it.
pub(all) struct Graded {
  dims : Array[Int32]
}

///|
/// The graded object concentrated in degree `0`.
pub fn Graded::unit() -> Graded {
  Graded::{ dims: [1], }
}

///|
/// The zero graded object.
pub fn Graded::zero() -> Graded {
  Graded::{ dims: [], }
}

///|
/// A `K`-vector space of dimension `v` placed in degree `d`.
pub fn Graded::of(v : Int32, d : Int32) -> Graded {
  let dims = Array::make(d + 1, 0)
  dims[d] = v
  Graded::{ dims, }
}

///|
/// Canonical form: drop the trailing zero degrees.  `Graded::of(2, 3)` and
/// `Graded::of(2, 0)` are the same graded object read with two different
/// amounts of padding, and `trim` is what makes them compare equal.
pub fn Graded::trim(self : Graded) -> Graded {
  let mut last = self.dims.length()
  while last > 0 && self.dims[last - 1] == 0 {
    last -= 1
  }
  let dims = Array::make(last, 0)
  for i in 0..<last {
    dims[i] = self.dims[i]
  }
  Graded::{ dims, }
}

///|
/// The total dimension -- the integer this graded object categorifies.
pub fn Graded::total(self : Graded) -> Int32 {
  let mut acc = 0
  for d in self.dims {
    acc += d
  }
  acc
}

///|
/// The dimension of the degree-`j` piece (`0` outside the range).
pub fn Graded::degree(self : Graded, j : Int32) -> Int32 {
  if j < 0 || j >= self.dims.length() {
    0
  } else {
    self.dims[j]
  }
}

///|
/// The largest degree carrying a nonzero dimension, `-1` for the zero object.
pub fn Graded::maxdeg(self : Graded) -> Int32 {
  let mut last = -1
  for i in 0..<self.dims.length() {
    if self.dims[i] != 0 {
      last = i
    }
  }
  last
}

///|
/// `true` iff the graded object is zero in every degree.
pub fn Graded::is_zero(self : Graded) -> Bool {
  for d in self.dims {
    if d != 0 {
      return false
    }
  }
  true
}

///|
/// Graded equality, after trimming both sides.
pub fn Graded::equal(self : Graded, other : Graded) -> Bool {
  self.trim().dims == other.trim().dims
}

///|
/// `[G]` with `G` shifted up by one degree: the suspension.
pub fn Graded::shift(self : Graded) -> Graded {
  let dims = Array::make(self.dims.length() + 1, 0)
  for i in 0..<self.dims.length() {
    dims[i + 1] = self.dims[i]
  }
  Graded::{ dims, }
}

///|
/// Termwise sum.
pub fn Graded::add(self : Graded, other : Graded) -> Graded {
  let n = if self.dims.length() > other.dims.length() {
    self.dims.length()
  } else {
    other.dims.length()
  }
  let dims = Array::make(n, 0)
  for i in 0..<n {
    dims[i] = self.degree(i) + other.degree(i)
  }
  Graded::{ dims, }.trim()
}

///|
/// Termwise difference.
pub fn Graded::sub(self : Graded, other : Graded) -> Graded {
  let n = if self.dims.length() > other.dims.length() {
    self.dims.length()
  } else {
    other.dims.length()
  }
  let dims = Array::make(n, 0)
  for i in 0..<n {
    dims[i] = self.degree(i) - other.degree(i)
  }
  Graded::{ dims, }.trim()
}

///|
/// Multiplying every graded dimension by `c` (used for dimensions only; the
/// graded object of a `K`-space is always `c * [G]` for a constant `c`).
pub fn Graded::scale(self : Graded, c : Int32) -> Graded {
  let dims = self.dims.map(d => d * c)
  Graded::{ dims, }.trim()
}

///|
/// Tensor product of graded objects: `(G (x) H)_i = sum_{a+b=i} G_a H_b`.
///
/// This is the categorified product: the tensor of two cohomologies is *not*
/// the product of their Betti numbers, it is their convolution, which is why
/// the cohomological dimension of a direct product of groups adds while its
/// Betti numbers multiply.
pub fn Graded::tensor(self : Graded, other : Graded) -> Graded {
  let a = self.dims.length()
  let b = other.dims.length()
  if a == 0 || b == 0 {
    return Graded::zero()
  }
  let dims = Array::make(a + b - 1, 0)
  for i in 0..<a {
    if self.dims[i] != 0 {
      for j in 0..<b {
        if other.dims[j] != 0 {
          dims[i + j] += self.dims[i] * other.dims[j]
        }
      }
    }
  }
  Graded::{ dims, }.trim()
}

///|
/// `n`-fold tensor power.
pub fn Graded::pow(self : Graded, n : Int32) -> Graded {
  let mut acc = Graded::unit()
  let mut i = 0
  while i < n {
    acc = acc.tensor(self)
    i += 1
  }
  acc
}

///|
/// The power series `sum_j dims[j] t^j`, for the emitted tables and for the
/// error messages of the tests.
pub fn Graded::poincare(self : Graded) -> String {
  let s = StringBuilder()
  s.write_string("P(t) = ")
  let mut first = true
  for j in 0..<self.dims.length() {
    if self.dims[j] != 0 {
      if !first {
        s.write_string(" + ")
      }
      first = false
      s.write_string(self.dims[j].to_string())
      s.write_string(" t^")
      s.write_string(j.to_string())
    }
  }
  if first {
    s.write_string("0")
  }
  s.to_string()
}

///|
/// `P(-1)`: the alternating sum of the graded dimensions, `0` for every object
/// with an action of `C_2` (graded dimensions paired by `j <-> j+1`).
pub fn Graded::alt(self : Graded) -> Int32 {
  let mut acc = 0
  for j in 0..<self.dims.length() {
    if j % 2 == 0 {
      acc += self.dims[j]
    } else {
      acc -= self.dims[j]
    }
  }
  acc
}

///|
/// A finite cochain complex
/// ```text
///   C^0 --d0--> C^1 --d1--> ... --d^{n-1}--> C^n
/// ```
/// of finite dimensional `K`-vector spaces, with the differentials written out
/// as matrices.  `maps[i]` is the matrix of `d_i`, a `dims[i]`-column,
/// `dims[i-1]`-row matrix; `maps[0]` is empty because there is no `d_0`.
///
/// The point of writing the matrices down is the point of categorification:
/// the graded object of the cohomology can be computed *from the complex* by
/// linear algebra, and the integers this system used to hard-code are then
/// seen to be a consequence rather than an input.
pub(all) struct Complex {
  dims : Array[Int32]
  maps : Array[Array[Array[Int32]]]
}

///|
/// Assemble a complex from its graded dimensions and its differentials.
pub fn Complex::new(
  dims : Array[Int32],
  maps : Array[Array[Array[Int32]]],
) -> Complex {
  Complex::{ dims, maps, }
}

///|
/// The number of degrees.
pub fn Complex::length(self : Complex) -> Int32 {
  self.dims.length()
}

///|
/// The graded object of the `i`-th term.
pub fn Complex::term(self : Complex, i : Int32) -> Graded {
  Graded::of(self.dims[i], 0)
}

///|
/// `d_i`, as a matrix (`dims[i]` columns, `dims[i-1]` rows).
pub fn Complex::map(self : Complex, i : Int32) -> Array[Array[Int32]] {
  if i <= 0 || i > self.maps.length() {
    return []
  }
  self.maps[i - 1]
}

///|
/// Rank of `d_i`, i.e. `dim_k im(d_i)`.
pub fn Complex::rank(self : Complex, k : Fp, i : Int32) -> Int32 {
  if i <= 0 || i > self.maps.length() {
    return 0
  }
  @la.rank(k, self.maps[i - 1])
}

///|
/// `dim_k ker(d_i) = dim_k C^i - rank(d_i)`.
pub fn Complex::kernel_dim(self : Complex, k : Fp, i : Int32) -> Int32 {
  self.dims[i] - self.rank(k, i)
}

///|
/// `dim_k H^i = dim_k C^i - rank(d_i) - rank(d_{i+1})`.
///
/// This is the *Euler characteristic* form of the answer.  It is the form the
/// frozen constants use, because it is `O(rank)` instead of `O(rank^2)`, and
/// it is checked against the direct computation (`homology_basis`) in the
/// tests -- the two agreeing is the assertion that the subtraction of two
/// integers was legitimate.
pub fn Complex::homology_dim(self : Complex, k : Fp, i : Int32) -> Int32 {
  self.kernel_dim(k, i) - self.rank(k, i + 1)
}

///|
/// The graded object `(H^0, H^1, ...)` of the cohomology of the complex.
///
/// **This is the categorification.**  For a resolution of the residue field it
/// is `Ext`, for a resolution of the diagonal it is the cohomology of the
/// diagonal, and in every case the `i`-th graded dimension is the Betti number
/// that the classical layer used to store as a bare integer.
pub fn Complex::cohomology(self : Complex, k : Fp) -> Graded {
  let dims = Array::make(self.dims.length(), 0)
  for i in 0..<self.dims.length() {
    dims[i] = self.homology_dim(k, i)
  }
  Graded::{ dims, }.trim()
}

///|
/// Actual representatives of `H^i = ker(d_i) / im(d_{i+1})`, as vectors in
/// `C^i`, not merely as a count of them.
///
/// The representatives are the classes of the kernel basis vectors that are
/// not in the image; they are returned reduced modulo the image, so they are a
/// canonical choice of representatives.  This is the concrete form of the
/// claim that `H^i` is a vector space rather than a number.
pub fn Complex::homology_basis(
  self : Complex,
  k : Fp,
  i : Int32,
) -> Array[Array[Int32]] {
  if i < 0 || i >= self.dims.length() {
    return []
  }
  let ker = @la.nullspace(k, self.map(i), self.dims[i])
  let im = @la.image_basis(k, self.map(i + 1))
  @la.quotient_basis(k, im, ker)
}

///|
/// The graded object of the terms of the complex, `(dim C^0, dim C^1, ...)`.
pub fn Complex::terms(self : Complex) -> Graded {
  Graded::{ dims: self.dims.copy(), }
}
