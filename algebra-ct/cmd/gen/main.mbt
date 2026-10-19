///|
type Fp = @poly.Fp

///|
type Poly = @poly.Poly

///|
type MTerm = @poly.MTerm

///|
/// `gen --p <prime> --n <nvars> --terms "e0. ... .en-1:coeff|...|..." --name <label>`
/// (polynomials separated by `;`, terms by `|`, exponents by `.`)
///
/// The compile-time driver of the whole system: it reads one algebraic
/// specification, runs the Gröbner engine on it, and writes the frozen
/// runtime package to stdout.  Nothing of the algebra survives into the
/// output; only the numbers it produced do.
fn main raise {
  let args = @env.args()
  let mut p = 97
  let mut n = 1
  let mut terms = "3.0:1|2.0:-6|1.0:11|0.0:-6"
  let mut name = "default"
  // `@env.args()` may or may not carry the program name, so scan for the
  // flags themselves instead of assuming a fixed stride.
  let mut i = 0
  while i < args.length() {
    let key = args[i]
    let mut val = ""
    let mut has = false
    if i + 1 < args.length() {
      val = args[i + 1]
      has = true
    }
    if key == "--p" && has {
      p = @string.parse_int(val)
      i += 2
    } else if key == "--n" && has {
      n = @string.parse_int(val)
      i += 2
    } else if key == "--terms" && has {
      terms = val
      i += 2
    } else if key == "--name" && has {
      name = val
      i += 2
    } else {
      i += 1
    }
  }
  let k = Fp::new(p)
  let gens = parse_terms(k, n, terms)
  if gens.length() == 0 {
    println("gen: no generators")
    return
  }
  // One Gröbner basis feeds all consumers: computing it once and passing it
  // down replaced three identical Buchberger runs.
  let (b, ps, qopt) = @quot.build_algebra(k, n, gens, @poly.Lex, POINT_BUDGET)
  let q = match qopt {
    Some(q) => q
    None => {
      println("gen: point enumeration exhausted its budget")
      return
    }
  }
  // Sanity check on the emitted cardinality.  A zero dimensional ideal whose
  // pure leading monomials all have degree <= d has `dim_k R/I <= d^n`, so a
  // violation means the standard-monomial enumeration and the Gröbner basis
  // disagree -- which is exactly the failure the frozen table must not ship.
  let d = b.pure_lead_degree()
  if d > 0 {
    let bound = ipow_sat(d, n)
    if bound < q.dim {
      println("gen: dimension \{q.dim} exceeds the Hilbert bound \{bound}")
      return
    }
  }
  let inv = @coho.analyse(k, n, gens, @poly.Lex, q, ps)
  // The categorified layer (T19): the graded objects behind those integers,
  // frozen into the same runtime table so the pointwise reading survives.
  let cat = @cat.categorify(q, ps)
  let stats = b.stats
  println(@emit.emit_runtime(k, q, stats, ps, inv, cat, name))
}

///|
/// Recursive cutting steps allowed while enumerating `V(I)`; mirrors
/// `quot.POINT_BUDGET`.
const POINT_BUDGET : Int32 = 200000

///|
/// `d^n` as an `Int`, saturating instead of overflowing: the Hilbert bound is
/// a sanity check, and a wrapped-around bound would defeat its purpose.
/// (`d^n` exceeds `Int32` for `d = 3, n = 20`.)
fn ipow_sat(d : Int32, n : Int32) -> Int32 {
  let mut acc : Int64 = 1
  let mut i = 0
  while i < n {
    acc = acc * d.to_int64()
    if acc > 2147483647 {
      return 2147483647
    }
    i += 1
  }
  acc.to_int()
}

///|
/// Parse the `--terms` argument into `Array[Poly]` with `n` variables.
///
/// Grammar (see `spec/spec.txt`):
/// ```text
///   polynomials  := polynomial (';' polynomial)*
///   polynomial   := term ('|' term)*
///   term         := exponent (':' coefficient)?
///   exponent     := int ('.' int)*        -- one entry per variable
/// ```
/// A leading `-` on the coefficient is allowed and every coefficient is read
/// modulo `p`, so a specification is prime-agnostic.  Malformed terms (no `:`)
/// are skipped rather than aborting the run.
fn parse_terms(k : Fp, n : Int32, spec : String) -> Array[Poly] raise {
  let out : Array[Poly] = []
  for poly in spec.split(";").to_array() {
    let ptext = poly.trim().to_owned()
    if ptext != "" {
      let pairs : Array[MTerm] = []
      for term in ptext.split("|").to_array() {
        let ttext = term.trim().to_owned()
        let parts = ttext.split(":").to_array()
        if parts.length() == 2 {
          let exps = parts[0].trim().split(".")
          let coef = @string.parse_int(parts[1].trim().to_owned())
          let m = Array::make(n, 0)
          let mut e = 0
          for ev in exps {
            if e >= n {
              break
            }
            m[e] = @string.parse_int(ev.trim().to_owned())
            e += 1
          }
          pairs.push((m, coef))
        }
      }
      if pairs.length() > 0 {
        out.push(Poly::from_pairs(k, n, pairs))
      }
    }
  }
  out
}
