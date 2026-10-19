///|
/// White-box tests for the shared linear algebra.
///
/// The four faces (`rank`, `span_basis`, `nullspace`, `quotient_basis`) are
/// answers to one arithmetic, so they are tested together and against each
/// other: every test checks that the *shape* of an answer agrees with the
/// dimension computed the other way round.

///|
fn k7() -> Fp {
  Fp::new(7)
}

///|
fn k97() -> Fp {
  Fp::new(97)
}

///|
fn k2() -> Fp {
  Fp::new(2)
}

///|
/// `M c = 0` for every row of `m`.
fn solves(k : Fp, m : Array[Array[Int32]], v : Array[Int32]) -> Bool {
  for row in m {
    let mut acc = 0
    let mut i = 0
    while i < v.length() {
      acc = k.add(acc, k.mul(row[i], v[i]))
      i += 1
    }
    if k.is_nonzero(acc) {
      return false
    }
  }
  true
}

///|
/// every coordinate of `v` is zero
fn is_zero(k : Fp, v : Array[Int32]) -> Bool {
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
/// `v` lies in the span of `rows`: adjoining `v` must not raise the rank.
fn in_span(k : Fp, rows : Array[Array[Int32]], v : Array[Int32]) -> Bool {
  let stacked = rows.map(r => r.copy())
  stacked.push(v.copy())
  rank(k, stacked) == rank(k, rows)
}

///|
test "regression: span_basis must return a full basis, not every second row" {
  let k = k7()
  let id2 = span_basis(k, [[1, 0], [0, 1]])
  assert_eq(id2.length(), 2)
  let id3 = span_basis(k, [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
  assert_eq(id3.length(), 3)
  let id4 = span_basis(k, [
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1],
  ])
  assert_eq(id4.length(), 4)
  // a dependent set has the dimension of its span, not of its row count
  let dep = span_basis(k, [[1, 1], [2, 2], [3, 3]])
  assert_eq(dep.length(), 1)
  // zero rows contribute nothing
  let z = span_basis(k, [[0, 0], [0, 0], [1, 2]])
  assert_eq(z.length(), 1)
  assert_true(span_basis(k, []).length() == 0)
}

///|
test "regression: nullspace of the empty system is all of K^cols" {
  let k = k7()
  let ns = nullspace(k, [], 3)
  assert_eq(ns.length(), 3)
  // a system of zero equations in zero unknowns has no solutions
  assert_eq(nullspace(k, [], 0).length(), 0)
  // rows of zero length: still no columns, still no unknowns
  assert_eq(nullspace(k, [[], [], []], 0).length(), 0)
  // <x*y>: the solutions are (a, b, c) with a = 0 or b = 0, a two-plane cone
  // whose kernel is the axis {a = b = 0}
  let ns2 = nullspace(k, [[0, 1, 0], [1, 0, 0]], 3)
  assert_eq(ns2.length(), 1)
  assert_eq(ns2[0], [0, 0, 1])
}

///|
test "regression: nullspace kernel is returned for a genuine singular system" {
  let k = k7()
  // rows [1 1 0], [2 2 0]: rank 1, so the kernel is the plane
  // {(t, -t, s)} -- two free coordinates, dimension 2.
  let m : Array[Array[Int32]] = [[1, 1, 0], [2, 2, 0]]
  let ns = nullspace(k, m, 3)
  assert_eq(ns.length(), 2)
  assert_eq(rank(k, m), 1)
  // the two basis vectors are linearly independent: no scalar multiple of
  // one is the other (checked over the whole field, not by a guessed minor)
  let mut independent = true
  let mut t = 0
  while t < k.p {
    let scaled = [k.mul(t, ns[0][0]), k.mul(t, ns[0][1]), k.mul(t, ns[0][2])]
    if scaled == ns[1] {
      independent = false
    }
    t += 1
  }
  assert_true(independent)
  // every returned vector really solves the system
  for v in ns {
    assert_true(solves(k, m, v))
  }
  let ns2 = nullspace(k, [[1, 2], [2, 4]], 2)
  assert_eq(ns2.length(), 1)
  assert_eq(k.add(ns2[0][0], k.mul(2, ns2[0][1])), 0)
}

///|
test "regression: nullspace back-substitutes along the pivot rows, not the discovery order" {
  let k = k2()
  // x + y + z = 0, x + y + w = 0 over F_2: the kernel is spanned by
  // (1,1,0,0) and (0,0,1,1).  Row 2 is zero, so a back-substitution that
  // indexed rows by *pivot discovery order* would read row 1 (the zero row)
  // instead of row 2 and return a wrong basis vector -- the regression this
  // test pins down.
  let m : Array[Array[Int32]] = [[1, 1, 1, 0], [0, 0, 0, 0], [1, 1, 0, 1]]
  let ker = nullspace(k, m, 4)
  assert_eq(ker.length(), 2)
  for v in ker {
    assert_true(solves(k, m, v))
  }
  assert_true(
    ker[0][0] != ker[1][0] ||
    ker[0][1] != ker[1][1] ||
    ker[0][2] != ker[1][2] ||
    ker[0][3] != ker[1][3],
  )
  assert_eq(ker[0], [1, 1, 0, 0])
  // the same shape in F_97 with non-unit leading coefficients
  let k97 = k97()
  let m2 : Array[Array[Int32]] = [[2, 4, 0, 0], [0, 0, 0, 0], [0, 0, 3, 6]]
  let ker2 = nullspace(k97, m2, 4)
  assert_eq(ker2.length(), 2)
  for v in ker2 {
    assert_true(solves(k97, m2, v))
  }
}

///|
test "matrix rank over a prime field" {
  let k = k97()
  let m0 : Array[Array[Int32]] = [[1, 2], [2, 4]] // dependent
  assert_eq(rank(k, m0), 1)
  let m1 : Array[Array[Int32]] = [[1, 0], [0, 1]]
  assert_eq(rank(k, m1), 2)
  let m2 : Array[Array[Int32]] = [[0, 0], [0, 0]]
  assert_eq(rank(k, m2), 0)
  assert_eq(rank(k, []), 0)
  // rank over F_2 counts mod 2: the first row of [[1,1],[1,1]] vanishes
  assert_eq(rank(k2(), [[1, 1], [1, 1]]), 1)
}

///|
test "rank + nullspace + image basis agree: dims add up" {
  let k = k97()
  let m : Array[Array[Int32]] = [[1, 2, 0], [2, 4, 1], [0, 0, 3]]
  let n = 3
  assert_eq(rank(k, m), 2) // det = 12 - 12 = 0, but the minor above is nonzero
  let r = rank(k, m)
  assert_eq(span_basis(k, m).length(), r)
  assert_eq(nullspace(k, m, n).length(), n - r)
  assert_eq(image_basis(k, m).length(), r)
  // a vector of the null space is orthogonal to every image vector: this is
  // the duality that lets `coho` read a rank off a kernel dimension
  // The two dualities, each with its own pairing: the kernel of a map is
  // orthogonal to its *row* space, and the image is orthogonal to the kernel
  // of the *transpose*.  (Pairing the kernel with the image would be a type
  // error -- the vectors do not even live in the same space.)
  for v in nullspace(k, m, n) {
    for w in span_basis(k, m) {
      let mut acc = 0
      let mut i = 0
      while i < w.length() {
        acc = k.add(acc, k.mul(w[i], v[i]))
        i += 1
      }
      assert_eq(acc, 0)
    }
  }
  for w in image_basis(k, m) {
    for v in nullspace(k, transpose(m), 3) {
      let mut acc = 0
      let mut i = 0
      while i < w.length() {
        acc = k.add(acc, k.mul(w[i], v[i]))
        i += 1
      }
      assert_eq(acc, 0)
    }
  }
}

///|
test "image_basis spans the columns, so its vectors live in the codomain" {
  let k = k7()
  // a wide, short matrix: rank 2, but the two answers have different lengths
  let m : Array[Array[Int32]] = [[1, 2, 3], [4, 5, 6]]
  let im = image_basis(k, m)
  let rowsp = span_basis(k, m)
  assert_eq(im.length(), rank(k, m))
  assert_eq(rowsp.length(), rank(k, m))
  assert_eq(im.length(), 2)
  // the row space sits in the domain (length 3), the image in the codomain
  for v in rowsp {
    assert_eq(v.length(), 3)
  }
  for v in im {
    assert_eq(v.length(), 2)
    assert_true(!is_zero(k, v))
  }
  // every column of `m` is a combination of the image basis
  for c in 0..<3 {
    let col = [m[0][c], m[1][c]]
    assert_true(in_span(k, im, col))
  }
}

///|
test "quotient_basis computes sup/sub as actual representatives" {
  let k = k97()
  // sub = span(e1) inside sup = span(e1, e2, e3): one free direction left
  let sub = [[0, 1, 0]]
  let sup = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]
  let q = quotient_basis(k, sub, sup)
  assert_eq(q.length(), 2)
  // every representative is outside `sub`
  for v in q {
    assert_true(!in_span(k, sub, v))
  }
  // the trivial quotients
  assert_eq(quotient_basis(k, [], []).length(), 0)
  assert_eq(quotient_basis(k, [], sup).length(), 3)
  assert_eq(quotient_basis(k, sup, sup).length(), 0)
  // and the residues really span the whole quotient: `sup` is recovered
  // from `sub` together with the returned representatives
  let rebuilt = sub.map(r => r.copy())
  for v in q {
    rebuilt.push(v)
  }
  assert_eq(rank(k, rebuilt), rank(k, sup))
}

///|
test "identity, mat_mul and mat_apply compose like matrices" {
  let k = k7()
  let id2 = identity(2)
  assert_eq(mat_mul(k, id2, [[1, 2], [3, 4]]), [[1, 2], [3, 4]])
  let a = [[1, 2], [3, 4]]
  let b = [[5, 6], [7, 1]]
  // a*b = [[1*5+2*7, 1*6+2*1], [3*5+4*7, 3*6+4*1]]
  //     = [[19, 8], [43, 22]] = [[5, 1], [1, 1]] mod 7
  assert_eq(mat_mul(k, a, b), [[5, 1], [1, 1]])
  // mat_apply is the same arithmetic on a single vector
  assert_eq(mat_apply(k, a, [1, 1]), [3, 0])
  assert_eq(mat_apply(k, identity(3), [4, 5, 6]), [4, 5, 6])
  assert_eq(identity(0).length(), 0)
}

///|
test "rref returns the reduced form with increasing pivot columns" {
  let k = k7()
  let m : Array[Array[Int32]] = [[0, 2, 4], [1, 0, 1], [1, 2, 5]]
  let (a, pivots) = rref(k, m)
  assert_eq(pivots, [0, 1])
  // every pivot column is a unit column: that is what "reduced" buys
  for i in 0..<pivots.length() {
    let mut j = 0
    while j < pivots.length() {
      assert_eq(a[i][pivots[j]], if i == j { 1 } else { 0 })
      j += 1
    }
  }
  // the reduced form still annihilates the same kernel
  for v in nullspace(k, m, 3) {
    assert_true(solves(k, a, v))
  }
  // the empty matrix reduces to itself
  let (e, ep) = rref(k, [])
  assert_eq(e.length(), 0)
  assert_eq(ep.length(), 0)
}
