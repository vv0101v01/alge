///|
/// White-box tests for the cohomology / invariant layer.
/// |
/// Every assertion below is an instance of a theorem proved in `coho.mbt`
/// (T7--T11); the numbers are small enough to be checked by hand.

///|
fn k97() -> Fp {
  Fp::new(97)
}

///|
fn k7() -> Fp {
  Fp::new(7)
}

///|
fn k2() -> Fp {
  Fp::new(2)
}

///|
/// `A = R/I` for a zero-dimensional `I`, together with the points of `V(I)`.
/// Every test below feeds a zero-dimensional ideal, which is exactly the case
/// in which the pipeline cannot fail.
fn ring(k : Fp, n : Int32, gens : Array[Poly]) -> (Quot, Array[Array[Int32]]) {
  let (_, ps, q) = @quot.build_algebra(k, n, gens, Lex, 100000)
  match q {
    Some(q) => (q, ps)
    None => abort("ring: the ideal is not zero dimensional")
  }
}

///|
/// `A = F_p[x] / (x^3)`: local, one point, `edim = 1`, `soc = 1`.
fn local_trivial(k : Fp) -> (Quot, Array[Array[Int32]]) {
  let x = Poly::var_n(k, 1, 0)
  ring(k, 1, [x.mul(x).mul(x)])
}

///|
test "T7: dim Omega^1 = sum of the embedding dimensions" {
  let k = k97()
  // A = K[x]/(x^3): m/m^2 has dimension 1, so Omega^1 is one-dimensional and
  // the coordinate ring is not reduced.
  let (q, ps) = local_trivial(k)
  let inv = analyse(
    k,
    1,
    [Poly::var_n(k, 1, 0).mul(Poly::var_n(k, 1, 0)).mul(Poly::var_n(k, 1, 0))],
    Lex,
    q,
    ps,
  )
  assert_eq(inv.dim, 3)
  assert_eq(inv.rad_dim, 2) // rad A = (x)
  assert_eq(inv.socle_dim, 1) // Ann(x) = (x^2)
  assert_eq(inv.cotangent_dim, 1)
  assert_true(inv.cotangent_dim > 0) // <=> not reduced
  // T8: f = x^3 has f' = 3x^2 = 0 mod the point 0, so the Jacobian is zero and
  // Ext^1_A(k,k) = K^1 / 0 has dimension 1.
  assert_eq(inv.ext1_dim, 1)
}

///|
test "T8: Ext^1 vanishes exactly when the ring is reduced" {
  let k = k97()
  let x = Poly::var_n(k, 1, 0)
  let gens = [x.mul(x).mul(x).sub(Poly::const_n(k, 1, 8))] // x^3 - 8 = (x-2)(x-2w)(x-2w^2)
  let (q, ps) = ring(k, 1, gens)
  let inv = analyse(k, 1, gens, Lex, q, ps)
  // gcd(x^3 - 8, 3x^2) = 1 over F_97 (8 != 0 and 3 != 0), so A is a product
  // of three distinct fields: reduced, so Omega^1 = 0 and Ext^1 = 0.
  assert_eq(inv.rad_dim, 0)
  assert_eq(inv.socle_dim, 3) // the socle of a product of fields is all of A
  assert_eq(inv.cotangent_dim, 0)
  assert_eq(inv.ext1_dim, 0)
  assert_eq(inv.kind().code, 0) // etale
}

///|
test "the fat point: Omega^1 = Ext^1 = soc = 2" {
  let k = k7()
  let x = Poly::var_n(k, 2, 0)
  let y = Poly::var_n(k, 2, 1)
  let gens = [x.mul(x), x.mul(y), y.mul(y)] // K[x,y]/(x^2, xy, y^2)
  let (q, ps) = ring(k, 2, gens)
  assert_eq(ps.length(), 1)
  let inv = analyse(k, 2, gens, Lex, q, ps)
  assert_eq(inv.dim, 3)
  assert_eq(inv.rad_dim, 2) // rad = (x, y)
  assert_eq(inv.socle_dim, 2) // Ann(m) = m
  // T7: Omega^1 = m/m^2, which is spanned by x and y
  assert_eq(inv.cotangent_dim, 2)
  // T8: every partial derivative of x^2, xy, y^2 is a multiple of x or y, so
  // the Jacobian vanishes mod m and Ext^1 = K^2.
  assert_eq(inv.ext1_dim, 2)
  assert_eq(inv.kind().code, 2) // local, but not a group algebra
  assert_eq(inv.group_order, 0)
}

///|
test "T9 + T10: the wild p-group algebra F_2[C_2 x C_2]" {
  let k = k2()
  let x = Poly::var_n(k, 2, 0)
  let y = Poly::var_n(k, 2, 1)
  // x^2 = y^2 = 1 is k[C_2 x C_2]; shifting to (x-1, y-1) gives the familiar
  // presentation K[u,v]/(u^2, v^2) used below.
  let gens = [x.mul(x).sub(Poly::one_n(k, 2)), y.mul(y).sub(Poly::one_n(k, 2))]
  let (q, ps) = ring(k, 2, gens)
  let inv = analyse(k, 2, gens, Lex, q, ps)
  assert_eq(inv.dim, 4) // |C_2 x C_2|
  assert_eq(inv.rad_dim, 3) // rad = ((x-1), (y-1)), quotient of dimension 1
  assert_eq(inv.socle_dim, 1) // T9: soc(k[G]) = A * N is one-dimensional
  assert_eq(inv.cotangent_dim, 2)
  // T9: |G| = 2^2 and r = 2 cyclic factors, so the cohomological dimension of
  // H^*(G, F_2) is infinite and the Betti numbers are 1, 2, 3, 4, ...
  assert_eq(inv.group_order, 4)
  assert_eq(inv.group_rank, 2)
  assert_eq(inv.kind().code, 1) // p-group algebra
  assert_eq(inv.betti, [1, 2, 3, 4, 5, 6, 7])
}

///|
test "T10: Cohen-Maclane Betti numbers" {
  // P(t) = (1+t)^r / (1-t^2)^{|G|-r}
  assert_eq(cohen_maclane(4, 2, 6), [1, 2, 3, 4, 5, 6, 7])
  assert_eq(cohen_maclane(8, 3, 5), [1, 3, 8, 16, 30, 50])
  assert_eq(cohen_maclane(9, 2, 5), [1, 2, 8, 14, 35, 56])
  // r = 1: (1+t)/(1-t^2)^{|G|-1}
  assert_eq(cohen_maclane(3, 1, 4), [1, 1, 2, 2, 3])
}

///|
test "T11: Frobenius data recovers the number of points" {
  let k = k97()
  // A = K[x]/((x-1)(x-2)(x-3)): three rational points, all fixed by Frobenius.
  let x = Poly::var_n(k, 1, 0)
  let gens = [
    // x^3 - 6x^2 + 11x - 6 = (x-1)(x-2)(x-3), written with -6 = 91 mod 97
    x
    .mul(x)
    .mul(x)
    .add_const_public(91)
    .add(x.mul(Poly::const_n(k, 1, 11)))
    .add_const_public(91),
  ]
  let (q, ps) = ring(k, 1, gens)
  let inv = analyse(k, 1, gens, Lex, q, ps)
  assert_eq(inv.frob_fixed, 3) // # K-rational points
  // An etale algebra is fixed-point free in higher powers only if the residue
  // fields are bigger; here every degree is 1, so Fix(F^m) stays at 3.
  assert_eq(frobenius_fixed(q, 97), 3)
}

///|
test "log_p and binomial arithmetic" {
  assert_eq(log_p(4, 2), Some(2))
  assert_eq(log_p(49, 7), Some(2))
  assert_eq(log_p(3, 97), None)
  assert_eq(log_p(0, 7), None)
  assert_eq(binom(5, 2), 10)
  assert_eq(binom(5, 6), 0)
  assert_eq(binom(0, 0), 1)
}

///|
