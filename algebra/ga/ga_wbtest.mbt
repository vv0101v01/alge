///|
fn cub() -> Tables {
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
  }
}

///|
fn fat() -> Tables {
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
  }
}

///|
test "the frozen tensor of A = K[x]/((x-1)(x-2)(x-3)) is a ring table" {
  let t = cub()
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
  let t = cub()
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
  let t = fat()
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
  let t = cub()
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
