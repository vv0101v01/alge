///|
type MTerm = @poly.MTerm

///|
fn k97() -> Fp {
  Fp::new(97)
}

///|
fn univ(k : Fp, terms : Array[MTerm]) -> Poly {
  Poly::from_pairs(k, 1, terms)
}

///|
fn mono(k : Fp, deg : Int32) -> Poly {
  Poly::from_mono(k, 1, [deg], 1)
}

///|
test "the multiplication table of A = K[x]/(x^3) is closed and unital" {
  let k = k97()
  let q = quotient_ring(k, 1, [mono(k, 3)], @poly.Lex)
  assert_eq(q.dim, 3)
  assert_eq(q.basis.length(), 3)
  // basis = 1, x, x^2
  let one = Array::make(3, 0)
  one[0] = 1
  let x = Array::make(3, 0)
  x[1] = 1
  let x2 = Array::make(3, 0)
  x2[2] = 1
  assert_eq(q.mul_coords(x, x), x2)
  assert_eq(q.mul_coords(x2, x), Array::make(3, 0)) // x^3 = 0
  assert_eq(q.mul_coords(one, x), x)
  // distributivity on one coordinate: (1+x) * x == x + x^2
  let sum = q.k.add(one[0], x[0])
  let _ = sum
  let onepx = Array::make(3, 0)
  onepx[0] = 1
  onepx[1] = 1
  let prod = q.mul_coords(onepx, x)
  assert_eq(prod[1], 1)
  assert_eq(prod[2], 1)
  assert_eq(prod[0], 0)
}

///|
test "a local Artin algebra is detected, with its embedding dimension" {
  let k = k97()
  let q = quotient_ring(k, 1, [mono(k, 3)], @poly.Lex)
  assert_true(q.is_local)
  assert_eq(q.point[0], 0)
  // edim = dim_k m/(I + m^2) with I = (x^3), m = (x): (x)/(x^2) has k-basis
  // {x}, so edim = 1 > dim A = 0 and the local ring K[x]_(x)/(x^3) is NOT
  // regular.  (Note dim A/(I + m^2) = 2, which is a different number.)
  assert_eq(q.edim, 1)
  // for the radical ideal <x> the maximal ideal is 0 and edim = 0: regular.
  let r = quotient_ring(k, 1, [mono(k, 1)], @poly.Lex)
  assert_true(r.is_local)
  assert_eq(r.edim, 0)
}

///|
test "Chinese remainder: three primitive idempotents of K[x]/((x-1)(x-2)(x-3))" {
  let k = k97()
  let f = univ(k, [([3], 1), ([2], k.neg(6)), ([1], 11), ([0], k.neg(6))])
  let q = quotient_ring(k, 1, [f], @poly.Lex)
  assert_eq(q.dim, 3)
  assert_true(!q.is_local) // three points, so the algebra is semisimple, not local
  let ps = match @gb.points(k, 1, [f], @poly.Lex, 100000) {
    Some(v) => v
    None => fail("budget")
  }
  assert_eq(ps.length(), 3)
  let es = primitive_idempotents(q, ps)
  assert_eq(es.length(), 3)
  let one = Array::make(q.dim, 0)
  one[0] = 1
  let sum = Array::make(q.dim, 0)
  for e in es {
    for i in 0..<q.dim {
      sum[i] = k.add(sum[i], e[i])
    }
  }
  assert_eq(sum, one) // sum_i e_i = 1
  for a in 0..<es.length() {
    // e_a^2 = e_a
    assert_eq(q.mul_coords(es[a], es[a]), es[a])
    // e_a is the characteristic function of its own point
    assert_eq(q.eval_coords(es[a], ps[a]), 1)
    for bidx in 0..<es.length() {
      if bidx != a {
        let prod = q.mul_coords(es[a], es[bidx])
        for v in prod {
          assert_eq(v, 0)
        }
      }
    }
  }
}

///|
test "a squarefree factor gives a product of fields, a repeated factor a nilpotent" {
  let k = k97()
  // (x-1)^2 : A = K[e]/(e^2) with e = x-1 nilpotent
  let f = univ(k, [([2], 1), ([1], k.neg(2)), ([0], 1)])
  let q = quotient_ring(k, 1, [f], @poly.Lex)
  assert_eq(q.dim, 2)
  assert_true(q.is_local)
  let nil = @gb.nilradical(k, 1, [f], @poly.Lex)
  assert_eq(nil.length(), 1)
  assert_true(nil[0].same(univ(k, [([1], 1), ([0], k.neg(1))])))
  assert_true(!@gb.is_radical(k, [f], @poly.Lex))
}

///|
test "right_inverse solves M X = Id for a surjective matrix" {
  let k = k97()
  // M = [[1, 2, 0], [0, 1, 3]] is 2 x 3 and surjective.
  let m = [[1, 2, 0], [0, 1, 3]]
  let r = 2
  let d = 3
  let x = right_inverse(k, m)
  // M * X = Id_r
  let mut a = 0
  while a < r {
    let mut b = 0
    while b < r {
      let mut acc = 0
      let mut j = 0
      while j < d {
        acc = k.add(acc, k.mul(m[a][j], x[j * r + b]))
        j += 1
      }
      assert_eq(acc, if a == b { 1 } else { 0 })
      b += 1
    }
    a += 1
  }
}

///|
test "edim is dim_k m/(I+m^2): 0 exactly at reduced points" {
  let k = k97()
  let x = Poly::var_n(k, 1, 0)
  // x^2 - 9 = (x-3)(x+3) over GF(97):  -9 = 88.  Both roots are reduced, so
  // the local ring is a field and edim = 0 (T4: regular).
  let f = x.mul(x).add_const_public(88)
  assert_eq(embedding_dimension(k, 1, [f], Lex, [3]), 0)
  assert_eq(embedding_dimension(k, 1, [f], Lex, [94]), 0)
  // p outside V(I): I + m = (1), no local ring
  assert_eq(embedding_dimension(k, 1, [f], Lex, [5]), 0)
  // a non-reduced point has m = 0 but m != 0, hence edim = 1
  let g = x.sub(Poly::const_n(k, 1, 3)).mul(x.sub(Poly::const_n(k, 1, 3)))
  assert_eq(embedding_dimension(k, 1, [g], Lex, [3]), 1)
  assert_eq(embedding_dimension(k, 1, [g], Lex, [4]), 0)
  // x^3: (x)/(x^2) has basis {x}
  assert_eq(embedding_dimension(k, 1, [mono(k, 3)], Lex, [0]), 1)
  // x^2 is a hypersurface: regular, edim = dim A = 1
  assert_eq(embedding_dimension(k, 1, [mono(k, 2)], Lex, [0]), 1)
  // two variables, I = <x + y, y^2> at (0,0): m = (y), so edim = 1 even
  // though neither x nor y is in I + m^2 -- the count of "x_i - p_i not in
  // I + m^2" would wrongly answer 2 here.
  let xv = Poly::var_n(k, 2, 0)
  let yv = Poly::var_n(k, 2, 1)
  assert_eq(embedding_dimension(k, 2, [xv.add(yv), yv.mul(yv)], Lex, [0, 0]), 1)
  // <xy> at the origin: m/m^2 has basis {x, y}
  assert_eq(embedding_dimension(k, 2, [xv.mul(yv)], Lex, [0, 0]), 2)
}
