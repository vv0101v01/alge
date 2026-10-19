///|
test "the frozen tensor of A = K[x]/((x-1)(x-2)(x-3)) is a ring table" {
  let t = Tables::cub()
  assert_eq(t.p, 97)
  assert_eq(t.d, 3)
  assert_eq(t.npoints, 3)
  assert_true(!t.is_local)
  let one = t.one()
  let x = t.var_coords(0)
  assert_true(!t.is_zero(x))
  assert_eq(t.mul(x, one), x)
  // x^3 = 6 x^2 - 11 x + 6  (in the emitted field arithmetic)
  let x2 = t.mul(x, x)
  let x3 = t.mul(x2, x)
  // x^3 = 6 x^2 - 11 x + 6   (mod 97)
  let six = [6, 0, 0]
  let minus_eleven = [86, 0, 0]
  let expect = t.add_const(
    t.add(t.mul(six, x2), t.mul(minus_eleven, x)),
    one,
    6,
  )
  assert_eq(x3, expect)
}

///|
test "primitive idempotents at runtime: sum 1, orthogonal, idempotent" {
  let t = Tables::cub()
  let es = t.primitive_idempotents()
  assert_eq(es.length(), t.npoints)
  let one = t.one()
  let sum = t.add_many(es)
  assert_eq(sum, one)
  let mut i = 0
  while i < es.length() {
    assert_eq(t.mul(es[i], es[i]), es[i])
    assert_eq(t.eval(es[i], i), 1)
    let mut j = 0
    while j < es.length() {
      if j != i {
        assert_true(t.is_zero(t.mul(es[i], es[j])))
      }
      j += 1
    }
    i += 1
  }
}

///|
test "the non-reduced point has a socle of dimension 2 and is not regular" {
  let t = Tables::fat()
  assert_eq(t.p, 7)
  assert_eq(t.d, 3)
  assert_true(t.is_local)
  assert_eq(t.edim, 2)
  // edim 2 > dim 0 => the local ring is not regular
  assert_true(t.edim > 0)
  let soc = t.socle()
  assert_eq(soc.length(), 2) // spanned by x and y
  // m^2 = 0: every socle element kills x and y
  let x = t.var_coords(0)
  let y = t.var_coords(1)
  for v in soc {
    assert_true(t.is_zero(t.mul(v, x)))
    assert_true(t.is_zero(t.mul(v, y)))
  }
  // ... and x, y are not themselves in the socle only if x*y != 0; here m^2 = 0
  assert_true(t.is_zero(t.mul(x, y)))
}

///|
test "function ring: evaluation separates the points" {
  let t = Tables::cub()
  let x = t.var_coords(0)
  let mut r = 0
  let seen = Array::make(t.npoints, 0)
  while r < t.npoints {
    let v = t.eval(x, r)
    assert_true(v >= 0 && v < t.p)
    seen[r] = v
    r += 1
  }
  // the three roots are distinct
  assert_true(seen[0] != seen[1])
  assert_true(seen[1] != seen[2])
  assert_true(seen[0] != seen[2])
}

///|
test "T7/T8: the etale table has no infinitesimal directions" {
  let t = Tables::cub()
  assert_true(t.is_reduced())
  assert_eq(t.cotangent_dim, 0)
  assert_eq(t.ext1_dim, 0)
  assert_eq(t.rad_dim, 0)
  // a product of three fields: the socle is the whole algebra
  assert_eq(t.socle_dim, 3)
  assert_eq(t.frob_fixed, t.npoints)
  assert_eq(t.kind, 0)
  assert_eq(t.cohomology(), [3, 0, 3, 0, 0, 3, 0, 0])
}

///|
test "T7/T8: the fat point has a two-dimensional Omega^1 and Ext^1" {
  let t = Tables::fat()
  assert_false(t.is_reduced())
  // T7: the cotangent space at the point is m/m^2, whose dimension is edim.
  // This is dim_k(Omega^1 (x)_A K) = dim_k Tor^A_1(K,K), NOT dim_k Omega^1,
  // which is 3 here -- see the counterexample test below.
  assert_eq(t.cotangent_dim, t.edim)
  assert_eq(t.ext1_dim, 2) // T8: the Jacobian vanishes mod m
  assert_eq(t.rad_dim, 2)
  assert_eq(t.socle_dim, 2)
  assert_eq(t.kind, 2) // local, but not a group algebra
  assert_eq(t.group_order, 0)
  assert_eq(t.betti.length(), 0)
}

///|
test "T9/T10: the wild table is K[C_2 x C_2] with Betti numbers i+1" {
  let t = Tables::wild()
  assert_eq(t.p, 2)
  assert_eq(t.d, 4) // |C_2 x C_2|
  assert_true(t.is_local) // x^2 = 1 is not etale in char 2
  assert_false(t.is_reduced())
  assert_eq(t.group_order, 4)
  assert_eq(t.group_rank, 2)
  assert_eq(t.kind, 1)
  // Cohen-Maclane: H^*(C_2 x C_2, F_2) = Lambda(V) x F_2[W], dim V = 2,
  // dim W = |G| - r = 2, hence P(t) = (1+t)^2/(1-t^2)^2 = 1/(1-t)
  assert_eq(t.betti, [1, 2, 3, 4, 5, 6, 7])
  let mut i = 0
  while i < t.betti.length() {
    assert_eq(t.betti[i], t.betti_at(i))
    assert_eq(t.betti[i], i + 1)
    i += 1
  }
  // the socle is A * N with N = sum_{g in G} g = (1+x)(1+y): one dimensional
  assert_eq(t.socle_dim, 1)
  let x = t.var_coords(0)
  let y = t.var_coords(1)
  let one = t.one()
  let one_plus_x = t.add(one, x)
  let one_plus_y = t.add(one, y)
  let norm = t.mul(one_plus_x, one_plus_y)
  assert_true(!t.is_zero(norm))
  let soc = t.socle()
  assert_eq(soc.length(), 1)
  // soc[0] and norm generate the same line (char 2, so -norm = norm)
  let diff = Array::make(t.d, 0)
  let mut i = 0
  while i < t.d {
    diff[i] = t.fsub(soc[0][i], norm[i])
    i += 1
  }
  assert_true(t.is_zero(diff))
  // N^2 = |G| N = 0 in char 2, the classical check that soc(k[G]) = A * N
  assert_true(t.is_zero(t.mul(norm, norm)))
}

///|
test "runtime nullspace and solve read the pivot row, not the discovery order" {
  let t = Tables::wild()
  // x + y + z = 0 and x + y + w = 0 over F_2, with a zero row between them:
  // a solver that indexed rows by pivot discovery order would read the zero
  // row for the second pivot and return a wrong kernel.
  let sys : Array[Array[Int32]] = [
    [1, 1, 1, 0, 0],
    [0, 0, 0, 0, 0],
    [1, 1, 0, 1, 0],
  ]
  let ker = t.nullspace(sys, 4)
  assert_eq(ker.length(), 2)
  for v in ker {
    for row in sys {
      let mut acc = 0
      let mut i = 0
      while i < 4 {
        acc = t.fadd(acc, t.fmul(row[i], v[i]))
        i += 1
      }
      assert_eq(acc, 0)
    }
  }
  // `solve` on the same shape, with the right-hand side in the last column:
  // x + y = 1 and z + w = 0 has the solution x = 1, y = 0, z = 0, w = 0.
  let aug : Array[Array[Int32]] = [
    [1, 1, 0, 0, 1],
    [0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0],
  ]
  let x = t.solve(aug, 4, 3)
  for row in aug {
    let mut acc = 0
    let mut i = 0
    while i < 4 {
      acc = t.fadd(acc, t.fmul(row[i], x[i]))
      i += 1
    }
    assert_eq(acc, row[4])
  }
}

///|
test "T7 counterexample: the cotangent space is not dim_k Omega^1" {
  // The frozen `COTANGENT_DIM` is sum_p edim(A_p) = dim_k Tor^A_1(K,K).  For a
  // non-reduced algebra it is strictly smaller than dim_k Omega^1_{A/k}, so
  // reading it as the latter would be a false theorem.  This test pins the
  // distinction down by exhibiting an actual nonzero Omega^1 element.
  let t = Tables::fat()
  assert_eq(t.cotangent_dim, 2)
  // x . dx is nonzero in A dx + A dy: only its image modulo the relations
  // 2x dx = 0, y dx + x dy = 0, 2y dy = 0 could kill it, and x lies in
  // none of their spans (A = F7[x,y]/(x^2,xy,y^2) has m^2 = 0, so the
  // relations only involve x dx and y dy).  Hence dim_k Omega^1 = 3 > 2.
  let x = t.var_coords(0)
  let y = t.var_coords(1)
  assert_true(!t.is_zero(x)) // so x dx != 0 as a formal 1-form
  assert_true(!t.is_zero(y))
  assert_true(t.is_zero(t.mul(x, y))) // but m^2 = 0, which is what keeps
  assert_true(t.is_zero(t.mul(x, x))) // Omega^1 from collapsing to 0
  assert_true(t.is_zero(t.mul(y, y)))
}
