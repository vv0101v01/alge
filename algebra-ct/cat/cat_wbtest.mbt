///|
/// White-box tests for the categorification layer.
///
/// Every assertion is an instance of a theorem proved in `cat.mbt`,
/// `res.mbt` or `ring.mbt`; the numbers are small enough to check by hand,
/// and each block names the frozen table it reproduces
/// (`cub` = `tables_cub`, `fat` = `tables_fat`, `wild` = `tables_wild`).

///|
/// `A = R/I` for a zero-dimensional `I`, together with the points of `V(I)`.
fn ring(
  k : Fp,
  n : Int32,
  gens : Array[@poly.Poly],
) -> (Quot, Array[Array[Int32]]) {
  let (_, ps, q) = @quot.build_algebra(k, n, gens, Lex, 100000)
  match q {
    Some(q) => (q, ps)
    None => abort("ring: the ideal is not zero dimensional")
  }
}

///|
/// The three frozen tables, rebuilt from their defining ideals.
///
/// * `fat`  -- `K[x,y] / (x^2, xy, y^2)` over `F_7`: `D = 3`, one point.
/// * `cub`  -- `K[x] / ((x-1)(x-2)(x-3))` over `F_97`: `D = 3`, three points.
/// * `wild` -- `K[x,y] / (x^2 - 1, y^2 - 1)` over `F_2`: `D = 4`, one point,
///   `= K[C_2 x C_2]`.
fn fat_ring() -> (Quot, Array[Array[Int32]]) {
  let k = Fp::new(7)
  let x = @poly.Poly::var_n(k, 2, 0)
  let y = @poly.Poly::var_n(k, 2, 1)
  ring(k, 2, [x.mul(x), x.mul(y), y.mul(y)])
}

///|
fn cub_ring() -> (Quot, Array[Array[Int32]]) {
  let k = Fp::new(97)
  let t = @poly.Poly::var_n(k, 1, 0)
  let g = t
    .mul(t)
    .mul(t)
    .sub(t.mul(t).scale(6))
    .add(t.scale(11))
    .sub(@poly.Poly::const_n(k, 1, 6))
  ring(k, 1, [g])
}

///|
fn wild_ring() -> (Quot, Array[Array[Int32]]) {
  let k = Fp::new(2)
  let x = @poly.Poly::var_n(k, 2, 0)
  let y = @poly.Poly::var_n(k, 2, 1)
  let o = @poly.Poly::one_n(k, 2)
  ring(k, 2, [x.mul(x).sub(o), y.mul(y).sub(o)])
}

///|
/// `mix` -- `K[x,y] / (x^2 - y, y^3)` over `F_3`: `D = 6`, one point, local,
/// `m = (x)` principal.  The non-homogeneous counterexample of T12/T13.
fn mix_ring() -> (Quot, Array[Array[Int32]]) {
  let k = Fp::new(3)
  let x = @poly.Poly::var_n(k, 2, 0)
  let y = @poly.Poly::var_n(k, 2, 1)
  let g1 = x.mul(x).sub(y)
  let g2 = y.mul(y).mul(y)
  ring(k, 2, [g1, g2])
}

///|
/// The number of entries of `d^i` that survive in `d^i * d^{i+1}`; zero for
/// every `i` is the assertion that the Koszul matrices form a complex, which
/// is the whole reason the cohomology below is a cohomology.
fn compositions_vanish(loc : Local) -> Int32 {
  let kz = koszul_complex(loc)
  let mut bad = 0
  for i in 1..<(kz.length() - 2) {
    let prod = @la.mat_mul(loc.k, kz.map(i), kz.map(i + 1))
    for r in 0..<prod.length() {
      for c in 0..<prod[0].length() {
        if prod[r][c] != 0 {
          bad += 1
        }
      }
    }
  }
  bad
}

// ---------------------------------------------------------------- Graded ----

///|
test "Graded: the algebra of graded objects behaves like polynomials" {
  let g = Graded::of(1, 0).add(Graded::of(1, 1))
  assert_eq(g.dims, [1, 1]) // 1 + t
  assert_eq(g.total(), 2)
  assert_eq(g.maxdeg(), 1)
  assert_eq(g.pow(2).dims, [1, 2, 1]) // (1 + t)^2
  assert_eq(g.tensor(g).dims, [1, 2, 1]) // (1 + t)^2 as a product
  assert_eq(Graded::of(2, 3).alt(), -2) // odd degree, so -2
  assert_eq(Graded::of(1, 1).alt(), -1) // odd, so -1
  assert_eq(Graded::of(0, 0).sub(Graded::of(1, 1)).dims, [0, -1])
  assert_true(Graded::zero().is_zero())
  // padding must not disguise a nonzero graded object
  assert_false(Graded::of(3, 9).is_zero())
  assert_eq(Graded::of(3, 9).maxdeg(), 9)
  assert_eq(Graded::of(3, 9).total(), 3)
  assert_eq(Graded::of(3, 9).degree(8), 0)
  assert_eq(Graded::of(1, 0).shift().dims, [0, 1])
  assert_eq(Graded::unit().poincare(), "P(t) = 1 t^0")
}

///|
test "Graded: trim drops trailing zeros but keeps the degree indices" {
  // the Loewy filtration of the wild factor is 1 + 2t + t^2; a trailing zero
  // is the same object, a leading one is not -- it would move every element
  let g = Graded::{ dims: [0, 0, 1, 2, 1, 0], }.trim()
  assert_eq(g.dims, [0, 0, 1, 2, 1])
  assert_eq(g.total(), 4)
  assert_eq(g.maxdeg(), 4)
}

// --------------------------------------------------------------- Koszul -----

///|
test "T16: the parameter cohomology of the fat point is 1 + 3t + 2t^2" {
  let (q, ps) = fat_ring()
  let loc = local_factor(q, ps, 0)
  assert_eq(loc.dim, 3) // D = 3
  assert_eq(loc.mdim, 2) // RAD_DIM = 2
  let kz = koszul_complex(loc)
  assert_eq(kz.terms().trim().dims, [3, 6, 3]) // d * C(2, i)
  assert_eq(compositions_vanish(loc), 0) // it is a complex
  assert_eq(parameter_cohomology(loc).dims, [1, 3, 2])
  // H^0 = A / m = K
  assert_eq(parameter_cohomology(loc).degree(0), 1)
}

///|
test "T16: the parameter cohomology of the wild group algebra is (1 + t)^3" {
  let (q, ps) = wild_ring()
  let loc = local_factor(q, ps, 0)
  assert_eq(loc.dim, 4) // D = 4 = |C_2 x C_2|
  assert_eq(loc.mdim, 3) // RAD_DIM = 3
  let kz = koszul_complex(loc)
  assert_eq(kz.terms().trim().dims, [4, 12, 12, 4])
  assert_eq(compositions_vanish(loc), 0)
  assert_eq(parameter_cohomology(loc).dims, [1, 3, 3, 1]) // = (1 + t)^3
}

///|
test "T16: a regular local factor has parameter cohomology 1" {
  // the cub table is etale: three reduced points, so each factor is K itself
  let (q, ps) = cub_ring()
  let locs = local_factors(q, ps)
  assert_eq(locs.length(), 3) // NPOINTS = 3
  let mut total = 0
  for loc in locs {
    assert_eq(loc.mdim, 0) // RAD_DIM = 0
    assert_eq(parameter_cohomology(loc).dims, [1])
    assert_eq(compositions_vanish(loc), 0)
    total += loc.dim
  }
  assert_eq(total, 3) // D = 3
}

///|
test "T16: the cohomology dimensions are the difference of two ranks" {
  // the fast Euler-characteristic form of `homology_dim` and the explicit
  // quotient basis must agree, degree by degree
  let (q, ps) = wild_ring()
  let loc = local_factor(q, ps, 0)
  let kz = koszul_complex(loc)
  let h = kz.cohomology(loc.k)
  for i in 0..<h.dims.length() {
    let basis = kz.homology_basis(loc.k, i)
    assert_eq(basis.length(), h.degree(i))
  }
}

// --------------------------------------------------------------- Loewy ------

///|
test "T17: the Loewy filtration of the fat point is 1 + 2t" {
  let (q, ps) = fat_ring()
  let loc = local_factor(q, ps, 0)
  let lw = loewy(loc)
  assert_eq(lw.dims, [1, 2]) // m^2 = 0
  assert_eq(lw.total(), loc.dim) // sum of the grades = dim A_p
  assert_eq(socle_graded(loc).total(), 2) // SOCLE_DIM = 2
  assert_eq(hilbert(q).dims, [1, 2]) // = Loewy, the basis being graded
}

///|
test "T17: the Loewy filtration of the wild group algebra is 1 + 2t + t^2" {
  let (q, ps) = wild_ring()
  let loc = local_factor(q, ps, 0)
  let lw = loewy(loc)
  assert_eq(lw.dims, [1, 2, 1]) // m = 3, m^2 = 1, m^3 = 0
  assert_eq(lw.total(), 4) // D = 4
  assert_eq(lw.total() - lw.dims[0], loc.mdim) // RAD_DIM = 3
  assert_eq(socle_graded(loc).total(), 1) // SOCLE_DIM = 1
  assert_eq(socle_graded(loc).degree(lw.maxdeg()), 1)
  assert_eq(hilbert(q).dims, [1, 2, 1])
  assert_eq(hilbert(q).total(), q.dim)
}

///|
test "T17: the Loewy length of the cub table is 1 everywhere" {
  let (q, ps) = cub_ring()
  let locs = local_factors(q, ps)
  let mut lw_total = 0
  for loc in locs {
    lw_total += loewy(loc).total()
  }
  assert_eq(lw_total, q.dim)
  assert_eq(locs.length(), 3)
}

// ----------------------------------------------------------- CM ring -------

///|
test "T18: the Cohen-Maclane ring of C_2 x C_2 has b_i = i + 1" {
  // GROUP_ORDER = 4 = 2^2, GROUP_RANK = r = 2, so w = 2 - 2 = 0? no:
  // n = log_2(4) = 2 and w = n - r = 0 would give a finite ring, so the
  // frozen table uses the *modular* group data: r = 2 and |G| = 4 give
  // w = 1 in the Tate convention (one conjugacy class per Sylow complement),
  // and (r, w) = (2, 2) is the wild group's parameter pair.  Either way the
  // graded dimensions are read off the ring and are checked below.
  let k = Fp::new(97)
  let ring = cm_ring(k, 2, 2, 6)
  let g = ring.gr()
  // b_i = i + 1 for i <= 13, the last two entries are the truncation
  for i in 0..<14 {
    assert_eq(g.degree(i), i + 1)
  }
  assert_eq(g.total(), 112)
  assert_true(ring.tate_ranks().equal(g)) // Tate ranks = graded dimensions
  assert_true(ring.has_unit())
  assert_true(ring.graded_commutative())
}

///|
test "T18: associativity holds on every triple that stays inside the range" {
  let k = Fp::new(97)
  // a small ring so that every triple is checked exhaustively, not sampled
  let ring = cm_ring(k, 1, 1, 4)
  assert_eq(ring.size(), 10)
  assert_true(ring.associative())
  // Lambda(k) (x) K[u]: the basis is e_i u^j, e_0 = 1, e_1^2 = 0, and the
  // only products that vanish are those with two `e_1` factors
  let e = ring.mul(ring.index_of(1, 0, 1, []), ring.index_of(1, 0, 1, []))
  assert_eq(e, [])
}

///|
test "T18: the product of two exterior generators picks up the Koszul sign" {
  let k = Fp::new(97)
  let ring = cm_ring(k, 2, 1, 2)
  let e0 = ring.index_of(1, 0, 1, []) // {0}
  let e1 = ring.index_of(1, 0, 2, []) // {1}
  let e01 = ring.index_of(2, 0, 3, []) // {0, 1}
  // {1} * {0} = - {0, 1}: the wedge sign is the Koszul sign
  assert_eq(ring.mul(e1, e0), [(e01, k.p - 1)])
  assert_eq(ring.mul(e0, e1), [(e01, 1)])
  assert_eq(ring.mul(e0, e0), [])
}

///|
test "T18: the Tate ranks of the wild table start 1, 2, 3, 4" {
  let k = Fp::new(2)
  let ring = cm_ring(k, 2, 2, 6)
  // the frozen `betti` array of `tables_wild` is [1, 2, 3, 4]
  let frozen = [1, 2, 3, 4]
  let got = ring.tate_ranks()
  for i in 0..<frozen.length() {
    assert_eq(got.degree(i), frozen[i])
  }
}

///|
/// T19: the categorified data that `emit` freezes into the runtime table.
test "T19: categorify returns the three graded objects with sum D" {
  for ring in [fat_ring(), wild_ring(), cub_ring()] {
    let (q, ps) = ring
    let c = categorify(q, ps)
    assert_eq(c.hilbert_total(), q.dim)
    assert_eq(c.nfactors, ps.length())
    let mut rad = 0
    let mut soc = 0
    let mut tot = 0
    for p in 0..<c.nfactors {
      let b = c.loewy_point(p)
      assert_eq(b[0], 1) // gr^0 = K
      assert_eq(c.mdim(p) + 1, c.dim_at(p))
      rad += c.mdim(p)
      soc += c.socle(p)
      for x in b {
        tot += x
      }
      // the parameter cohomology always starts at H^0 = K and is 1 exactly
      // when the local ring is regular
      let k = c.kozul_point(p)
      assert_eq(k[0], 1)
      assert_eq(k.length() == 1, c.mdim(p) == 0)
    }
    assert_eq(tot, q.dim) // the Loewy filtration is exhaustive
    // both are sums of sub-dimensions of `A`; note that `soc <= rad` fails for
    // an etale algebra, where `rad = 0` and `soc = K` in every factor
    assert_true(rad <= q.dim)
    assert_true(soc <= q.dim)
  }
}

///|
test "T19: the frozen blocks of the three tables have the expected shapes" {
  let (q, ps) = wild_ring()
  let c = categorify(q, ps)
  assert_eq(c.loewy_point(0), [1, 2, 1])
  assert_eq(c.kozul_point(0), [1, 3, 3, 1])
  assert_eq(c.mdim(0), 3)
  assert_eq(c.socle(0), 1)
  assert_eq(c.dim_at(0), 4)
  assert_eq(c.loewy_point(1), []) // out of range
  let (q2, ps2) = fat_ring()
  let f = categorify(q2, ps2)
  assert_eq(f.loewy_point(0), [1, 2])
  assert_eq(f.kozul_point(0), [1, 3, 2])
  let (q3, ps3) = cub_ring()
  let e = categorify(q3, ps3)
  assert_eq(e.nfactors, 3)
  assert_eq(e.loewy_point(2), [1])
  assert_eq(e.kozul_point(1), [1])
  assert_eq(e.mdim(0), 0)
}

///|
/// T12: the Loewy series equals the Hilbert function exactly when the
/// standard-monomial basis is graded, i.e. when the ideal is homogeneous.
test "T12: hilbert = loewy for homogeneous ideals, and mix breaks it" {
  // fat, wild: homogeneous ideals, graded standard basis -> equal series
  let (q1, ps1) = fat_ring()
  let f = categorify(q1, ps1)
  assert_eq(f.hilbert, f.loewy)
  let (q2, ps2) = wild_ring()
  let w = categorify(q2, ps2)
  assert_eq(w.hilbert, w.loewy)
  // mix: I = (x^2 - y, y^3) is not homogeneous, the standard basis
  // {1, y, y^2, x, xy, xy^2} is not graded, and the series differ
  let (q3, ps3) = mix_ring()
  let m = categorify(q3, ps3)
  assert_eq(m.hilbert_total(), 6)
  let mut tot = 0
  for x in m.loewy {
    tot += x
  }
  assert_eq(tot, 6) // both still sum to D
  assert_eq(m.hilbert, [1, 2, 2, 1])
  assert_eq(m.loewy, [1, 1, 1, 1, 1, 1])
  assert_true(m.hilbert != m.loewy)
}

///|
/// T13: the socle trichotomy read off the Loewy block, and the refutation of
/// "dim_k socle = 1 implies regular" by the zero-dimensional ring `mix`.
test "T13: pointwise socle trichotomy" {
  // a field: m = 0
  let (q0, ps0) = cub_ring()
  let c = categorify(q0, ps0)
  for p in 0..<c.nfactors {
    assert_eq(c.pt_kind_point(p), 0)
  }
  // fat: soc = m, both dim 2 -> Gorenstein, not a field
  let (q1, ps1) = fat_ring()
  let f = categorify(q1, ps1)
  assert_eq(f.pt_kind_point(0), 1)
  assert_eq(f.socle(0), f.mdim(0))
  // wild: soc dim 1 < m dim 3 -> neither
  let (q2, ps2) = wild_ring()
  let w = categorify(q2, ps2)
  assert_eq(w.pt_kind_point(0), 2)
  assert_true(w.socle(0) < w.mdim(0))
  // mix: soc dim 1, m dim 5 -> neither; the naive discriminator fails here
  let (q3, ps3) = mix_ring()
  let m = categorify(q3, ps3)
  assert_eq(m.pt_kind_point(0), 2)
  assert_eq(m.socle(0), 1)
  assert_eq(m.mdim(0), 5)
  assert_eq(m.dim_at(0), 6)
}

///|
/// T15: the Euler characteristic of the parameter cohomology is 1 for a field
/// and 0 otherwise -- with no regularity hypothesis, because the Euler
/// characteristic of a complex equals that of its homology.
test "T15: kozul Euler characteristic" {
  let (q0, ps0) = cub_ring()
  let c = categorify(q0, ps0)
  for p in 0..<c.nfactors {
    assert_eq(c.kozul_euler(p), 1) // (1-1)^0
    assert_eq(c.pt_kind_point(p), 0)
  }
  let (q1, ps1) = fat_ring()
  let f = categorify(q1, ps1)
  assert_eq(f.kozul_euler(0), 0) // 1 - 3 + 2
  let (q2, ps2) = wild_ring()
  let w = categorify(q2, ps2)
  assert_eq(w.kozul_euler(0), 0) // 1 - 3 + 3 - 1
  let (q3, ps3) = mix_ring()
  let m = categorify(q3, ps3)
  assert_eq(m.kozul_euler(0), 0) // 1 - 5 + 10 - 10 + 5 - 1
}
