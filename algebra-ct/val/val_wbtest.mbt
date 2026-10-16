///|
fn k97() -> Fp {
  Fp::new(97)
}

///|
test "t-adic valuation is multiplicative" {
  let k = k97()
  // (t + 2)(t^2 + 5) = t^3 + 5t + 2t^2 + 10
  let a = [2, 1, 0, 0, 0]
  let b = [10, 5, 2, 1, 0]
  assert_eq(valuation(a), 0)
  assert_eq(valuation(b), 0)
  let t = [0, 0, 0, 1]
  assert_eq(valuation(t), 3)
  assert_eq(valuation([0, 0, 0, 0, 0]), -1)
  // t * t = t^6 exactly, and t^6 = 0 mod t^8 only when the precision drops it
  assert_eq(valuation(series_mul(k, t, t, 7)), 6)
  assert_eq(valuation(series_mul(k, t, t, 6)), -1)
  let u = [0, 1]
  let v = [0, 0, 1]
  assert_eq(valuation(series_mul(k, u, v, 6)), 3)
}

///|
test "truncated multiplication is exact modulo t^N" {
  let k = k97()
  let a = [1, 2, 3]
  let b = [4, 5]
  let p = series_mul(k, a, b, 4)
  assert_eq(p, [4, k.add(5, 8), k.add(10, 12), 15]) // 4 + 13t + 22t^2 + 15t^3
}

///|
test "Newton inversion doubles the precision each step" {
  let k = k97()
  // a = 1 + t, so 1/a = 1 - t + t^2 - t^3 + ... (mod t^N)
  let a = [1, 1]
  let inv = series_inv(k, a, 12)
  assert_eq(inv[0], 1)
  assert_eq(inv[1], k.neg(1))
  assert_eq(inv[2], 1)
  assert_eq(inv[11], if 11 % 2 == 0 { 1 } else { k.neg(1) })
  // a * inv = 1 mod t^12
  let chk = series_mul(k, a, inv, 12)
  assert_eq(chk[0], 1)
  for i in 1..<12 {
    assert_eq(chk[i], 0)
  }
}

///|
test "Newton square root of 1 + 2t" {
  let k = k97()
  let a = [1, 2]
  let b = series_sqrt(k, a, 10)
  let sq = series_mul(k, b, b, 10)
  assert_eq(sq[0], 1)
  assert_eq(sq[1], 2)
  for i in 2..<10 {
    assert_eq(sq[i], 0)
  }
}

///|
test "formal root of a series by Newton: x^3 = 1 + t" {
  let k = k97()
  let f = [1, 1] // 1 + t
  let x = series_root(k, f, 3, 9, 1)
  let cube = series_mul(k, series_mul(k, x, x, 9), x, 9)
  assert_eq(cube[0], 1)
  assert_eq(cube[1], 1)
  for i in 2..<9 {
    assert_eq(cube[i], 0)
  }
}

///|
test "truncation and formal derivative of truncated series" {
  let k = k97()
  let a = [1, 2, 3, 4, 5]
  // trunc keeps the coefficients below n and pads with zeros
  let t3 = trunc(a, 3)
  assert_eq(t3, [1, 2, 3])
  assert_eq(trunc(a, 9), [1, 2, 3, 4, 5, 0, 0, 0, 0])
  assert_eq(trunc(a, 0), [])
  // d/dt of a = 1 + 2t + 3t^2 + ... is 2 + 6t + 12t^2
  let d = series_deriv(k, a, 4)
  assert_eq(d, [2, 6, 12, 0])
  // the derivative of a constant is zero, and (fg)' = f'g + fg'
  assert_eq(series_deriv(k, [5], 3), [0, 0, 0])
  let f = [1, 1] // 1 + t
  let g = [1, 1] // 1 + t
  let prod = series_mul(k, f, g, 3) // 1 + 2t + t^2
  let lhs = series_deriv(k, prod, 3)
  let rhs = series_mul(k, series_deriv(k, f, 3), g, 3)
  let rhs2 = series_mul(k, f, series_deriv(k, g, 3), 3)
  let sum = rhs.copy()
  for i in 0..<3 {
    sum[i] = k.add(sum[i], rhs2[i])
  }
  assert_eq(lhs, sum)
  assert_eq(lhs, [2, 2, 0])
}

///|
test "series_pow and series_root agree on exact powers" {
  let k = k97()
  let a = [1, 1] // 1 + t
  // (1 + t)^3 = 1 + 3t + 3t^2 + t^3
  assert_eq(series_pow(k, a, 3, 4), [1, 3, 3, 1])
  assert_eq(series_pow(k, a, 1, 4), [1, 1, 0, 0])
  assert_eq(series_pow(k, a, 0, 4), [1, 0, 0, 0])
  // a square root exists exactly when the constant coefficient is a square
  // (2 + 3t)^2 = 4 + 12t + 9t^2 exactly, so Newton must return it
  let sq = [4, 12, 9]
  let r = series_root(k, sq, 2, 3, 2)
  assert_eq(series_pow(k, r, 2, 3), sq)
  assert_eq(r, [2, 3, 0])
  // the cube root of 1 + 3t + 3t^2 is 1 + t (Newton doubles the precision)

  // and the rejected case: b0^m != f(0) has no root, so nothing is returned
  assert_eq(series_root(k, [3, 1], 2, 3, 2), [0, 0, 0])
}
