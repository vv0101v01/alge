///|
/// # Monomial orders
///
/// **Definition.** A *monomial order* on `N^n` is a total, `N^n`-compatible
/// and `N`-compatible (well-founded) order.  Compatibility means
/// `m > m'  =>  m * u > m' * u`, which is exactly what Gröbner's algorithm
/// needs: division must decrease a well-founded measure so it terminates.
///
/// **Lemma (existence).** Every `N^n` admits such an order, e.g. lex or
/// graded reverse lex; they are built here from the two elementary
/// comparisons below.
pub(all) enum Order {
  /// Pure lexicographic on `(e_1, ..., e_n)`.
  Lex
  /// Graded lex: compare `|m|` first, then lex.
  Grlex
  /// Graded reverse lex: compare `|m|` first, then compare the exponent
  /// vectors *from the back*, reversing each comparison.
  Grevlex
}

///|
/// Return `1` if `a > b`, `-1` if `a < b`, `0` if equal, for the given order.
pub fn cmp_mono(order : Order, a : Array[Int32], b : Array[Int32]) -> Int32 {
  let n = a.length()
  match order {
    Lex => {
      let mut i = 0
      while i < n {
        if a[i] != b[i] {
          return if a[i] > b[i] { 1 } else { -1 }
        }
        i = i + 1
      }
      0
    }
    Grlex => {
      let da = mono_total_degree(a)
      let db = mono_total_degree(b)
      if da != db {
        if da > db {
          1
        } else {
          -1
        }
      } else {
        cmp_mono(Lex, a, b)
      }
    }
    Grevlex => {
      let da = mono_total_degree(a)
      let db = mono_total_degree(b)
      if da != db {
        if da > db {
          1
        } else {
          -1
        }
      } else {
        // reverse lex: the *last* differing exponent decides, reversed.
        let mut i = n - 1
        while i >= 0 {
          if a[i] != b[i] {
            return if a[i] > b[i] { -1 } else { 1 }
          }
          i = i - 1
        }
        0
      }
    }
  }
}

///|
/// The order as a short tag, used as part of generated symbol names.
pub fn Order::tag(self : Order) -> String {
  match self {
    Lex => "lex"
    Grlex => "grlex"
    Grevlex => "grevlex"
  }
}
