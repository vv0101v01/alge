///|
type Fp = @poly.Fp

///|
/// # Linear algebra over a finite field
/// |
/// The whole system asks exactly four questions about a matrix over `K`:
///
/// - how big is its image? (`rank`, `image_basis`)
/// - what solves `M c = 0`? (`nullspace`)
/// - what is a basis of its row space? (`span_basis`)
/// - what is left of a subspace modulo a smaller one? (`quotient_basis`)
///
/// Those four used to be answered by three independent copies of Gaussian
/// elimination (in `gb`, `coho` and, implicitly, inside the invariant code).
/// They are all answers to the *same* arithmetic, so it is written once here,
/// in one reduction routine, and the callers only choose which face they need.
///
/// **The reduction convention.**  `rref` returns the reduced row echelon
/// form together with its pivot columns in increasing order.  Because the form
/// is fully reduced, the pivot column `pivots[i]` is the `i`-th unit vector
/// of the reduced matrix, which is what lets `nullspace` back-substitute by
/// *pivot index* -- the defect a rank-deficient row would otherwise cause.

///|
/// Reduced row echelon form of `m` and the list of its pivot columns.
///
/// Pivot columns are returned in strictly increasing order and the pivot of
/// column `pivots[i]` sits in row `i`, so the two lists can be zipped.
pub fn rref(
  k : Fp,
  m : Array[Array[Int32]],
) -> (Array[Array[Int32]], Array[Int32]) {
  let rows = m.length()
  if rows == 0 {
    return (m.map(r => r.copy()), [])
  }
  let cols = m[0].length()
  let a = m.map(r => r.copy())
  let pivots : Array[Int32] = []
  let mut r = 0
  let mut c = 0
  while r < rows && c < cols {
    let mut piv = -1
    let mut rr = r
    while rr < rows {
      if k.is_nonzero(a[rr][c]) {
        piv = rr
        break
      }
      rr += 1
    }
    if piv < 0 {
      c += 1
      continue
    }
    let tmp = a[r]
    a[r] = a[piv]
    a[piv] = tmp
    let inv = k.inv(a[r][c])
    let mut cc = c
    while cc < cols {
      a[r][cc] = k.mul(a[r][cc], inv)
      cc += 1
    }
    // Eliminate from *every* other row, above and below: that is what makes
    // the result reduced rather than merely echelon, and it is why the
    // trailing rows end up identically zero.
    let mut rr = 0
    while rr < rows {
      if rr != r && k.is_nonzero(a[rr][c]) {
        let f = a[rr][c]
        let mut cc2 = c
        while cc2 < cols {
          a[rr][cc2] = k.sub(a[rr][cc2], k.mul(f, a[r][cc2]))
          cc2 += 1
        }
      }
      rr += 1
    }
    pivots.push(c)
    r += 1
    c += 1
  }
  (a, pivots)
}

///|
/// Rank of `m`: the number of pivot columns of its reduced form.
pub fn rank(k : Fp, m : Array[Array[Int32]]) -> Int32 {
  let (_, pivots) = rref(k, m)
  pivots.length()
}

///|
/// A `K`-basis of the row space of `rows` (the nonzero rows of its reduced
/// form, which span exactly the same space as the input).
pub fn span_basis(k : Fp, rows : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let (a, pivots) = rref(k, rows)
  let out : Array[Array[Int32]] = []
  let mut i = 0
  while i < pivots.length() {
    out.push(a[i].copy())
    i += 1
  }
  out
}

///|
/// Null space basis of the homogeneous system `M c = 0` over `K`.
///
/// `cols` is passed explicitly because the empty system `M = []` carries no
/// column information on its own, and the null space of a system without
/// equations is all of `K^cols` -- reading `m[0]` would have panicked.
///
/// The returned vectors are indexed by the free columns in increasing order,
/// each normalised to a `1` in its own free position, which makes the answer a
/// *canonical* basis and not merely one of many.
pub fn nullspace(
  k : Fp,
  m : Array[Array[Int32]],
  cols : Int32,
) -> Array[Array[Int32]] {
  let (a, pivots) = rref(k, m)
  let is_pivot = Array::make(cols, false)
  for p in pivots {
    is_pivot[p] = true
  }
  let out : Array[Array[Int32]] = []
  let mut f = 0
  while f < cols {
    if !is_pivot[f] {
      let v = Array::make(cols, 0)
      v[f] = 1
      let mut pi = 0
      while pi < pivots.length() {
        v[pivots[pi]] = k.neg(a[pi][f])
        pi += 1
      }
      out.push(v)
    }
    f += 1
  }
  out
}

///|
/// Transpose of `m`, read row-major.
pub fn transpose(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  if m.length() == 0 {
    return []
  }
  let rows = m.length()
  let cols = m[0].length()
  let out : Array[Array[Int32]] = []
  let mut c = 0
  while c < cols {
    let row = Array::make(rows, 0)
    let mut r = 0
    while r < rows {
      row[r] = m[r][c]
      r += 1
    }
    out.push(row)
    c += 1
  }
  out
}

///|
/// A `K`-basis of the image (column space) of the linear map represented by
/// `m`, returned as vectors in the codomain.
///
/// The columns of `m` are the generators, so the answer is the span of its
/// transpose -- which is `span_basis` applied to `m^T`.
pub fn image_basis(k : Fp, m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  span_basis(k, transpose(m))
}

///|
/// A basis of the quotient space `sup / sub`, given a basis `sub` of `sub` and
/// a basis `sup` of `sup` as vectors in the *same* coordinate space, with
/// `sub ⊆ sup`.
///
/// Each vector of `sup` that is not already in `sub` survives, reduced modulo
/// `sub`; the survivors are returned.  This is the concrete form of "the
/// answer of the categorification layer": cycles of a differential modulo
/// boundaries, as actual vectors rather than as two integers subtracted.
pub fn quotient_basis(
  k : Fp,
  sub : Array[Array[Int32]],
  sup : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let cols = if sup.length() > 0 {
    sup[0].length()
  } else if sub.length() > 0 {
    sub[0].length()
  } else {
    0
  }
  // Reduce once against `sub`, keeping the reduced form of every survivor:
  // that both decides membership and gives the representative.
  let reduced = reduce_against(k, sub, sup, cols)
  span_basis(k, reduced)
}

///|
/// Reduce every vector of `sup` modulo the row space of `sub`; a vector that
/// reduces to zero is dropped, the others are returned in reduced form.
fn reduce_against(
  k : Fp,
  sub : Array[Array[Int32]],
  sup : Array[Array[Int32]],
  cols : Int32,
) -> Array[Array[Int32]] {
  let basis : Array[Array[Int32]] = []
  let pivots : Array[Int32] = []
  for v in sub {
    insert_reduced(k, basis, pivots, v.copy(), cols)
  }
  let out : Array[Array[Int32]] = []
  for v in sup {
    let r = reduce_vector(k, basis, pivots, v.copy(), cols)
    if is_zero_vector(k, r) {
      continue
    }
    out.push(r.copy())
    insert_reduced(k, basis, pivots, r, cols)
  }
  out
}

///|
/// `true` iff every coordinate of `v` is `0`.
fn is_zero_vector(k : Fp, v : Array[Int32]) -> Bool {
  let mut i = 0
  while i < v.length() {
    if k.is_nonzero(v[i]) {
      return false
    }
    i += 1
  }
  true
}

///|
/// Kill every pivot coordinate of `v` using the reduced basis rows.
fn reduce_vector(
  k : Fp,
  basis : Array[Array[Int32]],
  pivots : Array[Int32],
  v : Array[Int32],
  cols : Int32,
) -> Array[Int32] {
  let mut pi = 0
  while pi < pivots.length() {
    let p = pivots[pi]
    if k.is_nonzero(v[p]) {
      let f = v[p]
      let mut c = 0
      while c < cols {
        if basis[pi][c] != 0 {
          v[c] = k.sub(v[c], k.mul(f, basis[pi][c]))
        }
        c += 1
      }
    }
    pi += 1
  }
  v
}

///|
/// Add `v` to a reduced basis that is kept in echelon order: normalise `v` on
/// its first nonzero column, clear that column from every existing row and
/// splice the result into the pivot list.  Invariant maintained: `basis[i]`
/// has its first nonzero entry at `pivots[i]`, the pivots increase, and each
/// row is zero in every other pivot column.
fn insert_reduced(
  k : Fp,
  basis : Array[Array[Int32]],
  pivots : Array[Int32],
  v : Array[Int32],
  cols : Int32,
) -> Unit {
  let mut c = 0
  while c < cols && !k.is_nonzero(v[c]) {
    c += 1
  }
  if c >= cols {
    return
  }
  let inv = k.inv(v[c])
  let mut cc = 0
  while cc < cols {
    v[cc] = k.mul(v[cc], inv)
    cc += 1
  }
  let mut pi = 0
  while pi < basis.length() {
    if k.is_nonzero(basis[pi][c]) {
      let f = basis[pi][c]
      let mut c2 = 0
      while c2 < cols {
        if v[c2] != 0 {
          basis[pi][c2] = k.sub(basis[pi][c2], k.mul(f, v[c2]))
        }
        c2 += 1
      }
    }
    pi += 1
  }
  let mut pos = 0
  while pos < pivots.length() && pivots[pos] < c {
    pos += 1
  }
  basis.insert(pos, v)
  pivots.insert(pos, c)
}

///|
/// The `d x d` identity matrix.
pub fn identity(d : Int32) -> Array[Array[Int32]] {
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
/// Matrix product `a * b` over `K`, for rectangular `a`, `b` as well as square
/// ones.
///
/// **Shape.**  `a` is `m x n` and `b` is `n x p`, so the answer is `m x p`;
/// the inner extent `n` is read from `a` and the number of columns from `b`,
/// never from the row count.  Taking the shape from `a.length()` alone -- the
/// obvious shortcut -- silently computes a *square* product and indexes `b`
/// out of range as soon as the differentials of a complex have different
/// dimensions, which is the normal case for the maps between graded pieces
/// (`d^i` is `dim C^i`-by-`dim C^{i+1}`, rarely square).  An empty `a` or `b`
/// yields the empty product rather than a panic.
pub fn mat_mul(
  k : Fp,
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let rows = a.length()
  let inner = if rows > 0 { a[0].length() } else { 0 }
  let cols = if b.length() > 0 { b[0].length() } else { 0 }
  let out : Array[Array[Int32]] = []
  for i in 0..<rows {
    let row = Array::make(cols, 0)
    for j in 0..<cols {
      let mut acc = 0
      for t in 0..<inner {
        if a[i][t] != 0 && b[t][j] != 0 {
          acc = k.add(acc, k.mul(a[i][t], b[t][j]))
        }
      }
      row[j] = acc
    }
    out.push(row)
  }
  out
}

///|
/// `v` mapped by the matrix `m`: the `j`-th coordinate is `sum_i v_i m[i][j]`.
pub fn mat_apply(
  k : Fp,
  m : Array[Array[Int32]],
  v : Array[Int32],
) -> Array[Int32] {
  let rows = m.length()
  let out = Array::make(rows, 0)
  let mut i = 0
  while i < rows {
    let mut acc = 0
    let mut t = 0
    while t < v.length() {
      if m[i][t] != 0 && v[t] != 0 {
        acc = k.add(acc, k.mul(m[i][t], v[t]))
      }
      t += 1
    }
    out[i] = acc
    i += 1
  }
  out
}
