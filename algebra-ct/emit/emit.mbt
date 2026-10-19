///|
type Fp = @poly.Fp

///|
type Quot = @quot.Quot

///|
type GbStats = @gb.GbStats

///|
type Inv = @coho.Inv

///|
type Cat = @cat.Cat

///|
/// # Emitting the frozen runtime tables
///
/// The generated package contains **no algebra**: it contains the numbers the
/// algebra was used to compute.  Concretely, for `A = R/I` of dimension `d`
/// it emits
///
/// - `D = d`, the `K`-dimension of the coordinate ring,
/// - `BASIS`, the `d * n` exponents of the standard monomials,
/// - `MUL`, the `d * d * d` multiplication tensor,
/// - `POINTS`, the `K`-rational points of `V(I)` (one row per point),
/// - `EDIM`, `LOCAL`, the local-ring invariants,
/// - `RAD_DIM`, `SOCLE_DIM`, `COTANGENT_DIM`, `EXT1_DIM`, `FROB_FIXED`, the
///   cohomological invariants of `coho` (Kaehler differentials `Omega^1`,
///   `Ext^1_A(k,k)`, the socle, the Frobenius fixed space),
/// - `GROUP_ORDER`, `GROUP_RANK`, `KIND`, `betti`, the group-theoretic
///   reading of `A` together with the Betti numbers of `H^*(G,k)`,
/// - `COST`, the measured Gröbner statistics, kept so that the runtime can
///   assert that it is looking at the same system it was generated for.
///
/// **Cost model.**  Every emitted operation is an index computation:
/// `mul` is `O(d)` additions after one table read, `embed` is `O(d)`,
/// `eval` is `O(d * n)`.  The Gröbner basis that produced the table is
/// `O(d^2)` normal forms and never appears at runtime, which is the entire
/// point of the split.
pub fn cost_model(d : Int32, n : Int32, stats : GbStats) -> String {
  let s = StringBuilder()
  s.write_string("pub const RUNTIME_D : Int = ")
  s.write_string(d.to_string())
  s.write_string("\npub const RUNTIME_N : Int = ")
  s.write_string(n.to_string())
  s.write_string("\npub const PAIRS_SCREENED : Int = ")
  s.write_string(stats.pairs_screened.to_string())
  s.write_string("\npub const PAIRS_FORMED : Int = ")
  s.write_string(stats.spairs_formed.to_string())
  s.write_string("\npub const PAIRS_REJECTED : Int = ")
  s.write_string(
    (stats.spairs_chain_rejected + stats.spairs_product_rejected).to_string(),
  )
  s.write_string("\npub const NAIVE_PAIRS : Int = ")
  s.write_string(stats.naive_pairs().to_string())
  s.write_string("\n")
  s.to_string()
}

///|
/// The derived layer: everything `coho` knows about `A` as a frozen integer.
/// None of this is needed to *use* the algebra -- it is there so that the
/// cohomological signature of the system can be read off (and proved about) at
/// runtime for the price of a constant.
fn invariants(inv : Inv) -> String {
  let s = StringBuilder()
  s.write_string(
    "// ---- cohomological / isomorphism invariants (frozen) ----------------\n",
  )
  s.write_string("pub const RAD_DIM : Int = ")
  s.write_string(inv.rad_dim.to_string())
  s.write_string("\npub const SOCLE_DIM : Int = ")
  s.write_string(inv.socle_dim.to_string())
  s.write_string("\npub const COTANGENT_DIM : Int = ")
  s.write_string(inv.cotangent_dim.to_string())
  s.write_string("\npub const EXT1_DIM : Int = ")
  s.write_string(inv.ext1_dim.to_string())
  s.write_string("\npub const FROB_FIXED : Int = ")
  s.write_string(inv.frob_fixed.to_string())
  s.write_string("\npub const GROUP_ORDER : Int = ")
  s.write_string(inv.group_order.to_string())
  s.write_string("\npub const GROUP_RANK : Int = ")
  s.write_string(inv.group_rank.to_string())
  s.write_string(
    "\n/// 0 = etale (a product of finite fields), 1 = a p-group algebra,\n",
  )
  s.write_string(
    "/// 2 = local but not a group algebra.\npub const KIND : Int = ",
  )
  s.write_string(inv.kind().code.to_string())
  s.write_string(
    "\n/// dim_k H^i(G, k) for i = 0 .. NBETTI - 1 (empty unless GROUP_ORDER > 0).\n",
  )
  s.write_string("pub const NBETTI : Int = ")
  s.write_string(inv.betti.length().to_string())
  s.write_string("\npub let betti : Array[Int] = [")
  s.write_string(list_of(inv.betti))
  s.write_string("]\n\n")
  s.to_string()
}

///|
/// The categorified layer (T19): the graded objects that `coho` compressed into
/// integers, frozen as flat integer arrays so the runtime needs no algebra to
/// read them.  `hilbert` is the Hilbert function of `A`; `loewy` and `kozul`
/// are the Loewy layers and the parameter cohomology of each local factor,
/// concatenated with their block lengths, so a pointwise reading survives the
/// round trip.
fn categorised(cat : Cat) -> String {
  let s = StringBuilder()
  s.write_string(
    "\n/// Hilbert function of A: `hilbert[j]` = the number of standard monomials\n/// of total degree `j`, so `NHILBERT` is its length and\n/// `sum hilbert = D` is the recovery identity.\n",
  )
  s.write_string("pub const NHILBERT : Int = ")
  s.write_string(cat.hilbert.length().to_string())
  s.write_string("\npub let hilbert : Array[Int] = [")
  s.write_string(list_of(cat.hilbert))
  s.write_string("]\n")
  s.write_string(
    "\n/// Loewy layers `gr^i A_p = m^i/m^{i+1}`, concatenated over the points;\n/// `loewy_lens[p]` is the Loewy length of the `p`-th local factor, so\n/// `loewy_block(p)` is that factor's graded object.  `sum loewy = D`,\n/// `sum_{i>=1}` of a block is `dim_k m_p`, and its last entry is `soc A_p`:\n/// RAD_DIM and SOCLE_DIM are graded dimensions here, not separate facts.\n",
  )
  s.write_string("pub const NLOEWY : Int = ")
  s.write_string(cat.loewy.length().to_string())
  s.write_string("\npub let loewy : Array[Int] = [")
  s.write_string(list_of(cat.loewy))
  s.write_string("]\n")
  s.write_string("\npub let loewy_lens : Array[Int] = [")
  s.write_string(list_of(cat.loewy_lens))
  s.write_string("]\n")
  s.write_string(
    "\n/// Parameter cohomology `H^i` of the Koszul complex on the parameters of\n/// each local factor, concatenated over the points.  `kozul[0] = 1` always,\n/// because `H^0 = A_p/m_p = K`.\n",
  )
  s.write_string("pub const NKOSZUL : Int = ")
  s.write_string(cat.kozul.length().to_string())
  s.write_string("\npub let kozul : Array[Int] = [")
  s.write_string(list_of(cat.kozul))
  s.write_string("]\n")
  s.write_string("\npub let kozul_lens : Array[Int] = [")
  s.write_string(list_of(cat.kozul_lens))
  s.write_string("]\n")
  s.write_string("pub const NPOINTS_CAT : Int = ")
  s.write_string(cat.nfactors.to_string())
  s.write_string("\n\n")
  s.to_string()
}

///|
/// Render a flat `Array[Int]` as a MoonBit list literal.
fn list_of(a : Array[Int32]) -> String {
  let s = StringBuilder()
  let mut i = 0
  while i < a.length() {
    if i > 0 {
      s.write_string(", ")
    }
    s.write_string(a[i].to_string())
    i += 1
  }
  s.to_string()
}

///|
/// The whole generated source of the runtime package.
pub fn emit_runtime(
  k : Fp,
  q : Quot,
  stats : GbStats,
  ps : Array[Array[Int32]],
  inv : Inv,
  cat : Cat,
  spec_name : String,
) -> String {
  let d = q.dim
  let n = q.n
  let s = StringBuilder()
  // ---- header -------------------------------------------------------------
  s.write_string("/// Generated by arena/algebra-ct from spec `")
  s.write_string(spec_name)
  s.write_string("`.\n/// Do not edit: this file is the frozen output of the\n")
  s.write_string("/// compile-time Gröbner engine (see spec/spec.txt).\n")
  s.write_string("pub const P : Int = ")
  s.write_string(k.p.to_string())
  s.write_string("\npub const D : Int = ")
  s.write_string(d.to_string())
  s.write_string("\npub const NVAR : Int = ")
  s.write_string(n.to_string())
  s.write_string("\npub const EDIM : Int = ")
  s.write_string(q.edim.to_string())
  s.write_string("\npub const LOCAL : Bool = ")
  s.write_string(if q.is_local { "true" } else { "false" })
  s.write_string("\n\n")
  // ---- exponents ----------------------------------------------------------
  let exps = Array::make(d * n, 0)
  let mut i = 0
  while i < d {
    let mut v = 0
    while v < n {
      exps[i * n + v] = q.basis[i][v]
      v += 1
    }
    i += 1
  }
  s.write_string(
    "/// Exponent vectors of the standard monomial basis (`basis[i * NVAR + v]`).\n",
  )
  s.write_string("pub let basis : Array[Int] = [")
  s.write_string(list_of(exps))
  s.write_string("]\n\n")
  // ---- multiplication tensor ---------------------------------------------
  let mul = Array::make(d * d * d, 0)
  i = 0
  while i < d {
    let mut j = 0
    while j < d {
      let cell = q.table[i * d + j]
      let mut t = 0
      while t < d {
        mul[(i * d + j) * d + t] = cell[t]
        t += 1
      }
      j += 1
    }
    i += 1
  }
  s.write_string(
    "/// Flat tensor `mul_tensor[(i*D + j)*D + t]` = coords of `basis_i * basis_j` at `t`.\n",
  )
  s.write_string("pub let mul_tensor : Array[Int] = [")
  s.write_string(list_of(mul))
  s.write_string("]\n\n")
  // ---- points -------------------------------------------------------------
  let flat = Array::make(ps.length() * n, 0)
  let mut r = 0
  while r < ps.length() {
    let mut v = 0
    while v < n {
      flat[r * n + v] = ps[r][v]
      v += 1
    }
    r += 1
  }
  s.write_string(
    "/// K-rational points of V(I), one row of NVAR coordinates each (`points`).\n",
  )
  s.write_string("pub const NPOINTS : Int = ")
  s.write_string(ps.length().to_string())
  s.write_string("\npub let points : Array[Int] = [")
  s.write_string(list_of(flat))
  s.write_string("]\n\n")
  // ---- cohomological invariants -------------------------------------------
  s.write_string(invariants(inv))
  s.write_string(categorised(cat))
  // ---- runtime operations -------------------------------------------------
  s.write_string(runtime_ops)
  s.write_string("\n")
  s.write_string(cost_model(d, n, stats))
  s.to_string()
}

///|
/// The fixed part of the generated package: the operations.  They are the
/// only code in the system, and each is `O(1)` in the Gröbner sense.
let runtime_ops : String =
  #|/// `c * d'` for two coordinate vectors: one table read per nonzero term.
  #|pub fn mul(c : Array[Int], e : Array[Int]) -> Array[Int] {
  #|  let res = Array::make(D, 0)
  #|  let mut i = 0
  #|  while i < D {
  #|    if c[i] != 0 {
  #|      let base = i * D * D
  #|      let mut j = 0
  #|      while j < D {
  #|        if e[j] != 0 {
  #|          let coef = norm(c[i] * e[j])
  #|          if coef != 0 {
  #|            let cell = base + j * D
  #|            let mut t = 0
  #|            while t < D {
  #|              let v = mul_tensor[cell + t]
  #|              if v != 0 {
  #|                res[t] = norm(res[t] + coef * v)
  #|              }
  #|              t += 1
  #|            }
  #|          }
  #|        }
  #|        j += 1
  #|      }
  #|    }
  #|    i += 1
  #|  }
  #|  res
  #|}
  #|
  #|/// Field operations on `Int` with `P` prime.
  #|pub fn norm(a : Int) -> Int {
  #|  let r = a % P
  #|  if r < 0 { r + P } else { r }
  #|}
  #|
  #|pub fn fadd(a : Int, b : Int) -> Int { norm(a + b) }
  #|pub fn fsub(a : Int, b : Int) -> Int { norm(a - b) }
  #|pub fn fmul(a : Int, b : Int) -> Int { norm(a * b) }
  #|
  #|pub fn finv(a : Int) -> Int { fpow(a, P - 2) }
  #|
  #|pub fn fpow(a0 : Int, e : Int) -> Int {
  #|  let mut base = norm(a0)
  #|  let mut acc = 1
  #|  let mut k = e
  #|  while k > 0 {
  #|    if k % 2 == 1 { acc = norm(acc * base) }
  #|    base = norm(base * base)
  #|    k = k / 2
  #|  }
  #|  acc
  #|}
  #|
  #|/// The value of an element of A at a point of V(I): O(D * NVAR).
  #|pub fn eval(c : Array[Int], row : Int) -> Int {
  #|  let mut acc = 0
  #|  let mut i = 0
  #|  while i < D {
  #|    if c[i] != 0 {
  #|      let mut prod = 1
  #|      let mut v = 0
  #|      while v < NVAR {
  #|        let mut e = 0
  #|        while e < basis[i * NVAR + v] {
  #|          prod = fmul(prod, points[row * NVAR + v])
  #|          e += 1
  #|        }
  #|        v += 1
  #|      }
  #|      acc = fadd(acc, fmul(c[i], prod))
  #|    }
  #|    i += 1
  #|  }
  #|  acc
  #|}
  #|
  #|/// Coordinates of the constant `a`: the vector of a with `a` at BASIS[0].
  #|pub fn const_coords(a : Int) -> Array[Int] {
  #|  let out = Array::make(D, 0)
  #|  out[0] = norm(a)
  #|  out
  #|}
  #|
  #|/// Coordinates of `t^i` when the basis contains it, else `0`.
  #|pub fn var_coords(i : Int) -> Array[Int] {
  #|  let out = Array::make(D, 0)
  #|  let mut e = 0
  #|  while e < D {
  #|    let mut hit = true
  #|    let mut v = 0
  #|    while v < NVAR {
  #|      let want = if v == i { 1 } else { 0 }
  #|      if basis[e * NVAR + v] != want { hit = false }
  #|      v += 1
  #|    }
  #|    if hit { out[e] = 1 }
  #|    e += 1
  #|  }
  #|  out
  #|}
