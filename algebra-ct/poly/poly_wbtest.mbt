///|
/// White-box tests for the coordinate-ring kernel `K[x_1, ..., x_n]`.

///|
fn k97() -> Fp {
  Fp::new(97)
}

///|
fn x_of(k : Fp) -> Poly {
  Poly::var_n(k, 1, 0)
}

///|
fn x(k : Fp, i : Int32) -> Poly {
  Poly::var_n(k, 2, i)
}

///|
test "field axioms GF(97)" {
  let k = k97()
  assert_true(is_prime(k.p))
  assert_eq(k.mul(3, 33), 2)
  assert_eq(k.mul(k.inv(5), 5), 1)
  assert_eq(k.add(96, 5), 4)
  assert_eq(k.sub(0, 1), 96)
  assert_eq(k.norm(-1), 96)
  assert_true(k.is_primitive(k.find_primitive()))
}

///|
/// `prod (x - r)` over a list of residues, as a univariate polynomial.
fn univar_roots(k : Fp, rs : Array[Int32]) -> Poly {
  let mut f = Poly::one_n(k, 1)
  for r in rs {
    f = f.mul(lin(k, r)).monic(Lex)
  }
  f
}

///|
fn Fp::find_primitive(self : Fp) -> Int32 {
  let mut g = 2
  while g < self.p {
    if self.is_primitive(g) {
      return g
    }
    g += 1
  }
  1
}

///|
test "monomial order is a total order compatible with multiplication" {
  let a = [3, 0, 1]
  let b = [1, 3, 0]
  let c = [3, 1, 4]
  assert_true(cmp_mono(Lex, a, b) > 0)
  assert_true(cmp_mono(Lex, c, a) > 0)
  assert_true(cmp_mono(Lex, c, b) > 0)
  assert_true(cmp_mono(Grlex, a, b) > 0)
  // reverse lex disagrees with lex on equal-degree monomials
  assert_true(cmp_mono(Grevlex, a, b) < 0)
  // compatibility with the monoid operation, for all three orders
  let u = [2, 2, 1]
  assert_true(cmp_mono(Lex, mono_mul(a, u), mono_mul(b, u)) > 0)
  assert_true(cmp_mono(Grlex, mono_mul(a, u), mono_mul(b, u)) > 0)
  assert_true(cmp_mono(Grevlex, mono_mul(a, u), mono_mul(b, u)) < 0)
  // antisymmetry and reflexivity
  assert_eq(cmp_mono(Lex, a, b), -cmp_mono(Lex, b, a))
  assert_eq(cmp_mono(Grevlex, a, b), -cmp_mono(Grevlex, b, a))
  assert_eq(cmp_mono(Lex, a, a), 0)
}

///|
test "monomial arithmetic agrees with the semiring laws" {
  let a = [2, 3]
  let b = [1, 5]
  let u = [4, 1]
  assert_eq(mono_mul(a, b), mono_mul(b, a))
  assert_eq(mono_mul(a, mono_mul(b, u)), mono_mul(mono_mul(a, b), u))
  assert_eq(mono_mul(a, mono_one(2)), a)
  assert_eq(mono_mul(a, mono_one(2)), a)
  assert_eq(mono_lcm(a, b), [2, 5])
  assert_true(mono_div_by([2, 5], a))
  assert_true(mono_div([2, 5], a).unwrap() == [0, 2])
  assert_true(mono_div([1, 0], b) is None)
  assert_eq(mono_total_degree(a), 5)
  assert_eq(mono_key(a), mono_key(mono_parse(mono_key(a))))
}

///|
test "canonical form: a polynomial map never stores a zero coefficient" {
  let k = k97()
  let f = x(k, 0).add(x(k, 0)) // 2 x0
  assert_eq(f.num_terms(), 1)
  let g = f.sub(x(k, 0).add(x(k, 0)))
  assert_true(g.is_zero())
  assert_eq(g.num_terms(), 0)
  assert_eq(x(k, 0).add_const_public(0).num_terms(), 1)
}

///|
test "polynomial ring laws" {
  let k = k97()
  let a = x(k, 0).add_const_public(3)
  let b = x(k, 1).scale(5)
  let c = a.add(x(k, 0)).scale(2)
  assert_true(a.add(b).same(b.add(a)))
  assert_true(a.mul(b).same(b.mul(a)))
  assert_true(a.mul(b.add(c)).same(a.mul(b).add(a.mul(c))))
  assert_true(a.mul(Poly::one_n(k, 2)).same(a))
  assert_true(a.mul(Poly::zero_n(k, 2)).is_zero())
  assert_true(a.sub(a).is_zero())
}

///|

///|
test "multivariate division: f = q g + r with deg r < deg g" {
  let k = k97()
  let g = x(k, 0).add(x(k, 0)) // 2 x0
  let f = x(k, 0).scale(7).add(x(k, 1).scale(3)).add_const_public(5)
  let (q, r) = f.divrem(g, Lex)
  assert_true(f.same(q.mul(g).add(r)))
  assert_true(r.lead_mono(Lex)[0] < 1)
  // leading coefficient of g is invertible, so the remainder is canonical
  assert_true(r.show(Lex) == "3*x1 + 5")
}

///|
test "S-polynomial of a Groebner pair reduces to zero" {
  let k = k97()
  // G = {x0 - x1 + 1, x1} is a Groebner basis: S(f,g) = -x1^2 + x1
  // reduces to 0 modulo G.
  let f = x(k, 0).sub(x(k, 1)).add_const_public(1)
  let g = x(k, 1)
  let s = f.s_poly(g, Lex)
  let r = s.normal_form([f, g], Lex)
  assert_true(r.is_zero())
  // a pair that is *not* a basis pair does not reduce to zero
  let h = x(k, 0)
  let r2 = f.s_poly(h, Lex).normal_form([f, h], Lex)
  assert_true(!r2.is_zero())
}

///|
test "derivative and evaluation agree with the chain rule" {
  let k = k97()
  let f = x(k, 0).mul_mono(mono_var(2, 1)).mul_mono(mono_var(2, 1)) // x0 x1^2
  assert_true(f.derivative(1).show(Lex) == "2*x0*x1")
  assert_true(f.derivative(0).show(Lex) == "x1^2")
  assert_eq(f.eval_at([3, 5]), 3 * 5 * 5)
}

///|
test "univariate gcd is a greatest common divisor" {
  let k = k97()
  let a = Poly::from_pairs(k, 1, [([3], 1), ([0], 1)]) // x^3 + 1
  let b = Poly::from_pairs(k, 1, [([1], 1), ([0], 1)]) // x + 1
  let g = gcd_univar(a, b)
  assert_true(b.divrem(g, Lex).1.is_zero())
  assert_true(a.divrem(g, Lex).1.is_zero())
  assert_true(g.monic(Lex).same(lin(k, 96)))
}

///|
test "factorization of a square-free polynomial over GF(97)" {
  let k = k97()
  // (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
  let f = Poly::from_pairs(k, 1, [
    ([3], 1),
    ([2], k.neg(6)),
    ([1], 11),
    ([0], k.neg(6)),
  ])
  let fs = factor_univar(k, f)
  assert_eq(fs.length(), 3)
  for e in fs {
    assert_eq(e.1, 1)
    assert_eq(e.0.deg1(), 1)
    assert_true(f.divrem(e.0, Lex).1.is_zero())
  }
  assert_eq(roots_in_field(k, f).length(), 3)
  assert_true(roots_in_field(k, f).contains(1))
  assert_true(roots_in_field(k, f).contains(3))
}

///|
test "factorization detects multiplicities" {
  let k = k97()
  // (x-1)^2 (x-4)
  let f = Poly::from_pairs(k, 1, [
    ([3], 1),
    ([2], k.neg(6)),
    ([1], 9),
    ([0], k.neg(4)),
  ])
  let fs = factor_univar(k, f)
  assert_eq(fs.length(), 2)
  let mut m1 = 0
  let mut m2 = 0
  for e in fs {
    if e.0.deg1() == 1 && roots_in_field(k, e.0).contains(1) {
      m1 = e.1
    }
    if roots_in_field(k, e.0).contains(4) {
      m2 = e.1
    }
  }
  assert_eq(m1, 2)
  assert_eq(m2, 1)
}

///|
test "a degree-3 irreducible factor is not split further" {
  let k = k97()
  // x^3 + x + 1 has no root in GF(97) => irreducible (cubic)
  let f = Poly::from_pairs(k, 1, [([3], 1), ([1], 1), ([0], 1)])
  assert_eq(roots_in_field(k, f).length(), 0)
  let fs = factor_univar(k, f)
  assert_eq(fs.length(), 1)
  assert_eq(fs[0].0.deg1(), 3)
}

///|
test "regression: is_prime accepts 2 and rejects composites" {
  assert_true(is_prime(2))
  assert_true(is_prime(3))
  assert_true(is_prime(5))
  assert_true(is_prime(97))
  assert_true(is_prime(7919))
  assert_false(is_prime(0))
  assert_false(is_prime(1))
  assert_false(is_prime(4))
  assert_false(is_prime(9))
  assert_false(is_prime(97 * 97))
}

///|
test "regression: is_primitive uses g^(n/q) for every prime divisor q of n" {
  // mod 7, 6 = 2*3: 3 is primitive, 6 has order 2 and must be rejected.
  let k = Fp::new(7)
  assert_true(k.is_primitive(3))
  assert_false(k.is_primitive(6))
  assert_false(k.is_primitive(1))
  assert_false(k.is_primitive(2))
  // every element counted as primitive really generates K^times
  let mut g = 1
  while g < 7 {
    if k.is_primitive(g) {
      let seen : Map[Int32, Bool] = Map([])
      let mut cur = 1
      let mut i = 0
      while i < 6 {
        cur = k.mul(cur, g)
        seen.set(cur, true)
        i += 1
      }
      assert_eq(seen.length(), 6)
    }
    g += 1
  }
  // the same for 97, where 96 = 2^5 * 3 leaves a leftover prime factor
  let k97 = Fp::new(97)
  let mut h = 2
  while h < 97 {
    if k97.is_primitive(h) {
      let seen2 : Map[Int32, Bool] = Map([])
      let mut cur = 1
      let mut i = 0
      while i < 96 {
        cur = k97.mul(cur, h)
        seen2.set(cur, true)
        i += 1
      }
      assert_eq(seen2.length(), 96)
    }
    h += 1
  }
}

///|
test "regression: equal_degree_split exponent no longer overflows Int32" {
  // p^5 overflows Int32, but the Cantor-Zassenhaus exponent (p^d - 1)/2
  // is congruent to (p-1)/2 in every case, so degree-5 splitting still works.
  let k = k97()
  let f = factor_univar(k, univar_roots(k, [2, 3, 5, 7, 11]))
  let mut deg = 0
  for (g, m) in f {
    deg += g.deg1() * m
  }
  assert_eq(deg, 5)
  assert_eq(f.length(), 5)
}

///|
test "divrem_list reduces by every divisor in turn and returns the quotients" {
  let k = k97()
  let x0 = x(k, 0)
  let x1 = x(k, 1)
  // G = { x^2 - y , y^2 - 1 }  in K[x,y]
  let g1 = x0.mul(x0).sub(x1)
  let g2 = x1.mul(x1).add_const_public(96)
  let f = x0.mul(x0).sub(x1.mul(x1.mul(x1)))
  let (qs, r) = f.divrem_list([g1, g2], Lex)
  assert_eq(qs.length(), 2)
  // f = q1*g1 + q2*g2 + r, so the reconstruction is exact
  let back = qs[0].mul(g1).add(qs[1].mul(g2)).add(r)
  assert_true(back.same(f))
  // the remainder is a normal form: reducing it again changes nothing
  let (qz2, r2) = r.divrem_list([g1, g2], Lex)
  assert_true(qz2[0].is_zero() && qz2[1].is_zero())
  assert_true(r2.same(r))
  let gz = Poly::zero_n(k, 2)
  let (qz, rz) = f.divrem_list([gz], Lex)
  assert_true(qz[0].is_zero())
  assert_true(rz.same(f))
}

///|
test "constant_value and is_nonzero_constant agree with the sparse form" {
  let k = k97()
  let c = Poly::const_n(k, 2, 42)
  assert_true(c.is_nonzero_constant())
  assert_eq(c.constant_value(), 42)
  assert_eq(Poly::const_n(k, 2, 97).num_terms(), 0) // zero is not stored
  let mixed = x(k, 0).add_const_public(7)
  assert_false(mixed.is_nonzero_constant())
  assert_false(Poly::zero_n(k, 2).is_nonzero_constant())
}

///|
test "univariate helpers: pow_mod_univar, lcm_univar, radical_part" {
  let k = k97()
  let f = univar_roots(k, [1, 2, 3]) // (x-1)(x-2)(x-3), monic, square-free
  let one = Poly::one_n(k, 1)
  // a^e mod m by square-and-multiply
  assert_true(pow_mod_univar(Poly::const_n(k, 1, 7), 0, f).same(one))
  assert_true(
    pow_mod_univar(Poly::const_n(k, 1, 7), 1, f).same(Poly::const_n(k, 1, 7)),
  )
  assert_true(
    pow_mod_univar(Poly::const_n(k, 1, 7), 2, f).same(Poly::const_n(k, 1, 49)),
  )
  assert_true(pow_mod_univar(f, 1, f).is_zero())
  assert_true(pow_mod_univar(f, 2, f).is_zero())
  // lcm is monic and a common multiple
  let g = univar_roots(k, [3, 5])
  let l = lcm_univar(f, g)
  assert_true(l.same(l.monic(Lex)))
  assert_true(l.divrem(f, Lex).1.is_zero())
  assert_true(l.divrem(g, Lex).1.is_zero())
  assert_true(lcm_univar(f, Poly::zero_n(k, 1)).same(f))
  assert_true(lcm_univar(Poly::zero_n(k, 1), g).same(g))
  // radical of a square-free polynomial is itself
  assert_true(radical_part(f).same(f))
  // (x-1)^2 (x-2): radical = (x-1)(x-2)
  let h = lin(k, 1).mul(lin(k, 1)).mul(lin(k, 2)).monic(Lex)
  assert_true(radical_part(h).same(univar_roots(k, [1, 2])))
  assert_true(radical_part(Poly::const_n(k, 1, 5)).same(one))
}

///|
test "split_linear and distinct_irreducible factor f over GF(p)" {
  let k = k97()
  let rs = [4, 11, 60]
  let f = univar_roots(k, rs)
  let parts = split_linear(k, f)
  assert_eq(parts.length(), 3)
  let mut prod = Poly::one_n(k, 1)
  for l in parts {
    assert_true(l.monic(Lex).deg1() == 1)
    prod = prod.mul(l)
  }
  assert_true(prod.monic(Lex).same(f))
  // distinct irreducibles of the radical agree up to order
  let irr = distinct_irreducible(k, f)
  assert_eq(irr.length(), 3)
  let mut prod2 = Poly::one_n(k, 1)
  for q in irr {
    assert_true(q.monic(Lex).deg1() == 1)
    prod2 = prod2.mul(q)
  }
  assert_true(prod2.monic(Lex).same(f))
  // an irreducible quadratic over GF(7) has no roots and no linear factors:
  // 3 is a quadratic non-residue mod 7 (the residues are 1, 2, 4)
  let k7 = Fp::new(7)
  let irred = x_of(k7).mul(x_of(k7)).add_const_public(4) // x^2 - 3
  assert_true(irred.monic(Lex).deg1() == 2)
  assert_eq(split_linear(k7, irred).length(), 0)
  assert_eq(distinct_irreducible(k7, radical_part(irred)).length(), 1)
  assert_true(
    distinct_irreducible(k7, irred)[0].monic(Lex).same(irred.monic(Lex)),
  )
  // a reducible quadratic splits into exactly its two linear factors
  let red = x_of(k7).mul(x_of(k7)).add_const_public(5) // (x-1)(x+1)
  assert_eq(split_linear(k7, red).length(), 2)
}
