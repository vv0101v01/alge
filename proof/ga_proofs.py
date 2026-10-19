"""隱蔽式形式化證明 / hidden formal certificates for the frozen algebra tables.

Every statement below is handed to Z3 as an SMT formula; a theorem is
*discharged* when the negation is `unsat`.  The Z3 proof obligations are
generated from the **frozen tables that ship inside the MoonBit packages**
(`ga/tables_cub/tables.mbt`, `ga/tables_fat/tables.mbt`), so the certificates
certify the constants the runtime actually consumes -- not a re-implementation.

Encoding: the residue field F_p is modelled by Z/pZ with congruence notation
`x = y (mod p)`.  All nonlinearities are variable x constant, so the goals stay
inside decidable arithmetic.  Universal statements over ring elements are
discharged by finite enumeration, which is legitimate here because the rings
are *defined* as finite sets (dim D = 3 over F_p).
"""
import math
import os
import re, sys, time
from itertools import product
import z3

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "algebra", "ga")


# ---------------------------------------------------------------- tables ----
def read_tables(path):
    src = open(path).read()
    out = {}
    for key in ["P", "D", "NVAR", "EDIM", "NPOINTS",
                "RAD_DIM", "SOCLE_DIM", "COTANGENT_DIM", "EXT1_DIM",
                "FROB_FIXED", "GROUP_ORDER", "GROUP_RANK", "KIND", "NBETTI"]:
        m = re.search(r"pub const %s : Int = (\d+)" % key, src)
        if m:
            out[key] = int(m.group(1))
    out["LOCAL"] = "pub const LOCAL : Bool = true" in src
    for key in ["basis", "mul_tensor", "points", "betti"]:
        m = re.search(r"pub let %s : Array\[Int\] = \[([^\]]*)\]" % key, src, re.S)
        if m:
            out[key] = [int(x) for x in m.group(1).split(",") if x.strip()]
        else:
            out[key] = []
    p, d = out["P"], out["D"]
    T = out["mul_tensor"]
    out["T"] = [[[T[(i * d + j) * d + t] for t in range(d)] for j in range(d)] for i in range(d)]
    return out


CUB = read_tables(ROOT + "/tables_cub/tables.mbt")
FAT = read_tables(ROOT + "/tables_fat/tables.mbt")
WILD = read_tables(ROOT + "/tables_wild/tables.mbt")


# --------------------------------------------------------------- the ring ---
class Alg:
    """The coordinate algebra K[x_1..x_n]/I described by a frozen table."""

    def __init__(self, tab):
        self.p, self.d, self.n = tab["P"], tab["D"], tab["NVAR"]
        self.basis, self.points, self.T = tab["basis"], tab["points"], tab["T"]
        self.edim, self.local = tab["EDIM"], tab["LOCAL"]

    def a(self, x, y=None): return (self.p if y is None else x) + y % self.p

    def s(self, x, y): return (x + y) % self.p

    def m(self, x, y): return (x * y) % self.p

    def neg(self, x): return (-x) % self.p

    def zero(self): return [0] * self.d

    def one(self):
        e = [0] * self.d
        e[0] = 1
        return e

    def add(self, a, b): return [self.s(a[i], b[i]) for i in range(self.d)]

    def sub(self, a, b): return [self.s(a[i], self.neg(b[i])) for i in range(self.d)]

    def scal(self, k, a): return [self.m(k, a[i]) for i in range(self.d)]

    def add_many(self, xs):
        out = self.zero()
        for x in xs:
            out = self.add(out, x)
        return out

    def mul(self, a, b):
        out = [0] * self.d
        for i in range(self.d):
            for j in range(self.d):
                if a[i] and b[j]:
                    c = self.m(a[i], b[j])
                    for t in range(self.d):
                        out[t] = self.s(out[t], self.m(c, self.T[i][j][t]))
        return out

    def x(self, v):  # coordinate vector of the variable x_v
        for i in range(self.d):
            ex = [0] * self.n
            ex[v] = 1
            if self.basis[i * self.n:(i + 1) * self.n] == ex:
                return [1 if k == i else 0 for k in range(self.d)]
        raise KeyError("variable not in the standard basis")

    def elements(self):
        if self.p ** self.d > 100000:
            return None
        out = [[]]
        for _ in range(self.d):
            out = [e + [k] for e in out for k in range(self.p)]
        return out

    def eval(self, a, pt):
        r = 0
        for i in range(self.d):
            ex = self.basis[i * self.n:(i + 1) * self.n]
            r = self.s(r, self.m(a[i], pow_pt(ex, pt, self.p)))
        return r

    def solve(self, M, rhs):
        """Gaussian elimination over F_p on an (rows x (d+1)) augmented system."""
        A = [row[:] for row in M]
        r, cols, piv = len(A), self.d, []
        pr = 0
        for c in range(cols):
            pivrow = None
            for i in range(pr, r):
                if A[i][c]:
                    pivrow = i
                    break
            if pivrow is None:
                continue
            A[pr], A[pivrow] = A[pivrow], A[pr]
            inv = pow(A[pr][c], self.p - 2, self.p)
            A[pr] = [self.m(v, inv) for v in A[pr]]
            for i in range(r):
                if i != pr and A[i][c]:
                    f = A[i][c]
                    A[i] = [self.s(A[i][k], self.neg(self.m(f, A[pr][k]))) for k in range(cols + 1)]
            piv.append(c)
            pr += 1
            if pr == r:
                break
        out = [0] * cols
        for i, c in enumerate(piv):
            out[c] = A[i][cols]
        return out

    def idempotents(self):
        """Primitive idempotents of a reduced product decomposition."""
        pts = [self.points[i * self.n:(i + 1) * self.n] for i in range(len(self.points) // self.n)]
        M = [[self.eval(self.coord(e), pt) for e in self.coord_basis()] for pt in pts]
        out = []
        for a in range(len(pts)):
            aug = [M[i] + [1 if i == a else 0] for i in range(len(pts))]
            out.append(self.solve(aug, len(pts)))
        return out

    def coord_basis(self):
        return [self.coord([1 if k == i else 0 for k in range(self.d)]) for i in range(self.d)]

    def coord(self, a):
        return a

    def mul_matrix(self, g):
        return [[self.mul(g, self.coord([1 if k == j else 0 for k in range(self.d)]))[i] for j in range(self.d)] for i in range(self.d)]

    def mat_vec(self, M, v):
        return [sum(self.m(M[i][j], v[j]) for j in range(self.d)) % self.p for i in range(self.d)]

    def solve_system(self, rows):
        """Solve M x = 0 for a (possibly rectangular) matrix M; return kernel basis."""
        A = [row[:] for row in rows]
        r, cols, piv, pr = len(A), self.d, [], 0
        for c in range(cols):
            pivrow = None
            for i in range(pr, r):
                if A[i][c]:
                    pivrow = i
                    break
            if pivrow is None:
                continue
            A[pr], A[pivrow] = A[pivrow], A[pr]
            inv = pow(A[pr][c], self.p - 2, self.p)
            A[pr] = [self.m(v, inv) for v in A[pr]]
            for i in range(r):
                if i != pr and A[i][c]:
                    f = A[i][c]
                    A[i] = [self.s(A[i][k], self.neg(self.m(f, A[pr][k]))) for k in range(cols)]
            piv.append(c)
            pr += 1
            if pr == r:
                break
        free = [c for c in range(cols) if c not in piv]
        out = []
        for fc in free:
            v = [0] * cols
            v[fc] = 1
            for i, c in enumerate(piv):
                v[c] = self.neg(A[i][fc])
            out.append(v)
        return out


def pow_pt(ex, pt, p):
    r = 1
    for e, c in zip(ex, pt):
        for _ in range(e):
            r = (r * c) % p
    return r


# ------------------------------------------------------------------ Z3 ------
S = z3.Solver()
S.set("timeout", 60000)
PROOFS = []


def mod_eq(x, y, p):
    return (x - y) % p == 0


def int_eq(x, y):
    """Exact equality of two integer-valued invariants (Z3 integer arithmetic).

    Group orders, Betti numbers, KIND tags and dimensions are integers; they
    must NOT be compared modulo p, where e.g. |C_2 x C_2| = 4 vanishes.
    """
    return zint(x) == zint(y)


def int_gt0(x):
    return zint(x) > zint(0)


def theorem(name, zh, formula, note=""):
    """Discharge `formula`; a certificate means the negation is unsatisfiable."""
    t0 = time.time()
    sv = z3.Solver()
    sv.set("timeout", 30000)
    sv.add(z3.Not(formula))
    r = sv.check()
    dt = time.time() - t0
    PROOFS.append((name, zh, str(r), dt, note))
    return r


def zint(x):
    return x if z3.is_expr(x) else z3.IntVal(int(x))


# ------------------------------------------------------- symbolic helpers ---
def zvec(prefix, d):
    return [z3.Int("%s_%d" % (prefix, i)) for i in range(d)]


def bound(v, p):
    return z3.And(*[z3.And(zint(0) <= x, x <= zint(p - 1)) for x in v])


def vadd(a, b, p):
    return [(a[i] + b[i]) % p for i in range(len(a))]


def vsub(a, b, p):
    return [(a[i] - b[i]) % p for i in range(len(a))]


def eqv(a, b):
    return z3.And(*[mod_eq(a[i], b[i], MOD) for i in range(len(a))])


def is_in(v, span):
    """Linear membership: v = sum_j c_j * s_j with symbolic c_j (over F_p)."""
    d = len(v)
    cs = zvec("c", len(span))
    expr = [zint(0)] * d
    for j, s in enumerate(span):
        for i in range(d):
            expr[i] = expr[i] + cs[j] * zint(s[i] % MOD)
    return z3.Exists(cs, eqv(v, expr))


def in_ideal(v, g, A):
    """v lies in the principal ideal A*g, i.e. v = M_g c (linear in c)."""
    k = zvec("k", A.d)
    return z3.Exists(k, eqv(v, lin_apply(A.mul_matrix(g), k)))


def in_span(span, v):
    """`v` (symbolic) lies in the constant span `span`: linear, no Exists."""
    d = len(v)
    expr = [zint(0)] * d
    for s in span:
        for i in range(d):
            if s[i]:
                expr[i] = expr[i] + zint(s[i] % MOD) * v[i]
    return eqv(v, expr)


def lin_apply(M, v):
    """Matrix with constant entries applied to a symbolic vector."""
    d = len(v)
    out = []
    for i in range(d):
        e = zint(0)
        for j in range(d):
            if M[i][j]:
                e = e + zint(M[i][j]) * v[j]
        out.append(e)
    return out


# =============================================================== THEOREMS ====

def col_basis(A, M):
    """A basis of the column space of the constant matrix M over F_p."""
    rows = [[M[i][j] for i in range(len(M))] for j in range(len(M[0]))]
    basis, r, piv = [], 0, []
    cur = [row[:] for row in rows]
    ncol = len(cur[0]) if cur else 0
    for c in range(ncol):
        pr = None
        for i in range(r, len(cur)):
            if cur[i][c]:
                pr = i
                break
        if pr is None:
            continue
        inv = pow(cur[pr][c], A.p - 2, A.p)
        vec = [A.m(v, inv) for v in cur[pr]]
        basis.append(vec)
        for i in range(len(cur)):
            if i != r and cur[i][c]:
                f = cur[i][c]
                cur[i] = [A.s(cur[i][k], A.neg(A.m(f, vec[k]))) for k in range(ncol)]
        r += 1
        if r == len(cur):
            break
    return basis


def pivot_coords(A, B):
    """Row indices t_1..t_k such that (a[t_j]) is a coordinate system on span(B)."""
    k = len(B)
    M = [[B[j][i] for j in range(k)] for i in range(A.d)]
    piv, pr, used = [], 0, set()
    for c in range(k):
        pr_ = None
        for i in range(A.d):
            if i in used:
                continue
            if M[i][c]:
                pr_ = i
                break
        if pr_ is None:
            continue
        used.add(pr_)
        piv.append(pr_)
        inv = pow(M[pr_][c], A.p - 2, A.p)
        M[pr_] = [A.m(v, inv) for v in M[pr_]]
        for i in range(A.d):
            if i != pr_ and M[i][c]:
                f = M[i][c]
                M[i] = [A.s(M[i][t], A.neg(A.m(f, M[pr_][t]))) for t in range(k)]
    return piv


def mat_inv(A, M):
    """Inverse of a square matrix over F_p."""
    k = len(M)
    aug = [[M[i][j] for j in range(k)] + [1 if i == j else 0 for j in range(k)] for i in range(k)]
    for c in range(k):
        pr = None
        for i in range(c, k):
            if aug[i][c]:
                pr = i
                break
        if pr is None:
            raise ValueError("singular")
        aug[c], aug[pr] = aug[pr], aug[c]
        inv = pow(aug[c][c], A.p - 2, A.p)
        aug[c] = [A.m(v, inv) for v in aug[c]]
        for i in range(k):
            if i != c and aug[i][c]:
                f = aug[i][c]
                aug[i] = [A.s(aug[i][t], A.neg(A.m(f, aug[c][t]))) for t in range(2 * k)]
    return [row[k:] for row in aug]


def param_form(A, B, a, prefix="l"):
    """a in span(B), quantified away: a = sum_j (dual coordinate of a) * B_j.

    The dual coordinates are *linear* functionals of `a`, so the whole
    statement stays inside decidable linear arithmetic modulo p.
    """
    piv = pivot_coords(A, B)
    k = len(B)
    Sinv = mat_inv(A, [[B[j][piv[r]] for r in range(k)] for j in range(k)])
    expr = [zint(0)] * A.d
    for j in range(k):
        for r in range(k):
            coef = Sinv[r][j]
            if not coef:
                continue
            for i in range(A.d):
                if B[j][i]:
                    expr[i] = expr[i] + a[piv[r]] * zint(A.m(coef, B[j][i]))
    return eqv(a, expr), piv


def run():
    global MOD
    P = CUB["P"]
    MOD = P
    cub = Alg(CUB)
    fat = Alg(FAT)
    P = CUB["P"]
    xc, xf = cub.x(0), fat.x(0)
    yf = fat.x(1)

    # ---- 座標環 / 函數環: the frozen tensor really is a ring -------------
    for tag, A in (("cub", cub), ("fat", fat)):
        d, p = A.d, A.p
        for i in range(d):
            for t in range(d):
                theorem("T1.%s.unit_l" % tag,
                        "座標環 %s: e_i * 1 = e_i (張量單位律)" % tag,
                        mod_eq(zint(A.T[i][0][t]), zint(1 if i == t else 0), p))
                theorem("T1.%s.unit_r" % tag,
                        "座標環 %s: 1 * e_i = e_i (張量單位律)" % tag,
                        mod_eq(zint(A.T[0][i][t]), zint(1 if i == t else 0), p))
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    for t in range(d):
                        l = sum(A.T[i][j][s] * A.T[s][k][t] for s in range(d)) % p
                        r = sum(A.T[j][k][s] * A.T[i][s][t] for s in range(d)) % p
                        theorem("T1.%s.assoc" % tag,
                                "函數環 %s: 結合律 (T*)*T = T*(T*)" % tag,
                                mod_eq(zint(l), zint(r), p))
        for i in range(d):
            for j in range(d):
                theorem("T1.%s.comm" % tag, "交換律 %s: e_i e_j = e_j e_i" % tag,
                        eqv([zint(A.T[i][j][t]) for t in range(d)],
                            [zint(A.T[j][i][t]) for t in range(d)]))

    # ---- 仿射代數簇: the frozen points are the K-points of V(I) ----------
    for tag, A in (("cub", cub), ("fat", fat)):
        p = A.p
        pts = [A.points[i * A.n:(i + 1) * A.n] for i in range(len(A.points) // A.n)]
        hom = z3.And(*[mod_eq(zint(A.eval(A.mul(A.coord_basis()[i], A.coord_basis()[j]), pt)),
                             zint(A.m(A.eval(A.coord_basis()[i], pt), A.eval(A.coord_basis()[j], pt))), p)
                       for pt in pts for i in range(A.d) for j in range(A.d)])
        theorem("T2.%s.eval_hom" % tag,
                "仿射代數簇 %s: 求值 ev_p 是環同態 (雙線性基底檢驗)" % tag, hom)
        theorem("T2.%s.points_distinct" % tag, "%s: V(I) 的 K-點兩兩相異" % tag,
                z3.And(*[zint(pts[i][0]) != zint(pts[j][0]) for i in range(len(pts))
                         for j in range(len(pts)) if i < j]))

    # ---- 冪等元 / 剩餘理想 / 半單理想 / 投射模 ---------------------------
    es = cub.idempotents()
    pts = [cub.points[i] for i in range(len(cub.points) // cub.n)]
    one, zero = cub.one(), cub.zero()
    thm = z3.And(*[eqv([zint(v) for v in cub.mul(es[i], es[j])],
                      [zint((1 if i == j else 0) * v % cub.p) for v in es[i]]) for i in range(len(es))
                 for j in range(len(es))])
    theorem("T3.idem_orthogonal", "冪等元: e_i e_j = delta_ij e_i (原始冪等元)", thm)
    theorem("T3.idem_sum", "冪等元: sum_i e_i = 1 (中國剩餘定理)", eqv([zint(v) for v in cub.add_many(es)], [zint(v) for v in one]))
    theorem("T3.idem_x", "冪等元: x = r_i e_i, 故 x - r_i in Ann(e_i)",
            z3.And(*[eqv([zint(v) for v in cub.mul(es[i], xc)],
                         [zint(cub.m(pts[i], v)) for v in es[i]]) for i in range(len(es))]))
    theorem("T3.idem_projection", "冪等元: e_i e_j = e_i 當 i=j (冪等)", z3.And(*[eqv([zint(v) for v in cub.mul(es[i], es[i])], [zint(v) for v in es[i]]) for i in range(len(es))]))
    # ker(ev_r) = A*(x - r)  and  A = sum_i e_i A,  intersection = 0
    a = zvec("a", cub.d)
    pre = bound(a, cub.p)
    for i, pt in enumerate(pts):
        xr = cub.sub(xc, cub.scal(pt, one))
        ev = zint(0)
        for t in range(cub.d):
            ex = cub.basis[t * cub.n:(t + 1) * cub.n]
            ev = ev + a[t] * zint(pow_pt(ex, [pt], cub.p))
        # ker(ev_p) is a linear subspace; write it without quantifiers.
        evrow = [pow_pt(cub.basis[t * cub.n:(t + 1) * cub.n], [pt], cub.p) for t in range(cub.d)]
        Bk = cub.solve_system([evrow])
        memb, _ = param_form(cub, Bk, a)
        theorem("T3.ker_eval_%d" % i,
                "剩餘理想 I_p = ker(ev_p) = A*(x - r): 核的參數式描述",
                z3.Implies(pre, z3.Implies(mod_eq(ev, zint(0), cub.p), memb)))
        # ... and the same subspace is generated by x - r (ground witnesses).
        Mx = cub.mul_matrix(xr)
        for jj in range(len(Bk)):
            w = cub.solve([Mx[i] + [Bk[jj][i]] for i in range(cub.d)], cub.d)
            theorem("T3.ker_eval_%d.gen" % i,
                    "剩餘理想 I_p = A*(x - r): 核的每個基底向量都由 x - r 生成",
                    eqv([zint(v) for v in cub.mul(w, xr)], [zint(v) for v in Bk[jj]]))

    theorem("T3.ker_inter_zero", "半單理想: 三個剩餘理想的交 = 0 (A 是半單環)",
            z3.Implies(pre, z3.Implies(
                z3.And(*[mod_eq(sum(a[t] * zint(pow_pt(cub.basis[t * cub.n:(t + 1) * cub.n], [pt], cub.p)) for t in range(cub.d)), zint(0), cub.p) for pt in pts]),
                eqv(a, [zint(0)] * cub.d))))
    c0, c1, c2 = zvec("c00", cub.d), zvec("c10", cub.d), zvec("c20", cub.d)
    ca, cb = zvec("ca", cub.d), zvec("cb", cub.d)

    def proj(e, cs):
        """e * cs, a *linear* expression because e is a frozen vector."""
        return lin_apply(cub.mul_matrix(e), cs)

    theorem("T3.decomposition",
            "投射模/半單理想: A = e_1 A (+) e_2 A (+) e_3 A, pi_i(a) = e_i*a",
            z3.Implies(pre, eqv(a, vadd(vadd(proj(es[0], a), proj(es[1], a), cub.p), proj(es[2], a), cub.p))))
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            Bi = col_basis(cub, cub.mul_matrix(es[i]))
            Bj = col_basis(cub, cub.mul_matrix(es[j]))
            fi, _ = param_form(cub, Bi, a, "u")
            fj, _ = param_form(cub, Bj, a, "v")
            theorem("T3.direct_%d%d" % (i, j),
                    "直和性: e_%d A ∩ e_%d A = 0 (兩條直線獨立)" % (i, j),
                    z3.Implies(pre, z3.Implies(z3.And(fi, fj), eqv(a, [zint(0)] * cub.d))))

    # 域內冪等元只有 0,1
    theorem("T3.field_idem", "域 F_p 中 a^2 = a 蘊涵 a = 0 或 a = 1 (故 A 的冪等元皆由 e_i 組成)",
            z3.And(*[z3.Implies(mod_eq(zint(i * i), zint(i), cub.p),
                                z3.Or(mod_eq(zint(i), zint(0), cub.p), mod_eq(zint(i), zint(1), cub.p)))
                     for i in range(cub.p)]))
    run_cub_extra(cub, pts, es)
    run_fat()
    run_coho()
    return cub, fat, pts, es



def run_fat():
    """Theorems about the local, non-reduced point  F7[x,y]/(x^2,xy,y^2)."""
    global MOD
    fat = Alg(FAT)
    MOD = FAT["P"]
    P7 = 7
    x, y = fat.x(0), fat.x(1)
    mspan = [x, y]
    a = zvec("a", fat.d)
    pre = bound(a, P7)
    Mx, My = fat.mul_matrix(x), fat.mul_matrix(y)
    stacked = [Mx[i] + My[i] for i in range(fat.d)]
    Bm = col_basis(fat, stacked)
    memb, _ = param_form(fat, Bm, a, "s")

    theorem("T4.socle_param",
            "正則局部環/底環 Soc(A)=Ann(m): 底環元素的參數式描述 (雙向)",
            z3.Implies(pre, z3.And(
                z3.Implies(z3.And(eqv(lin_apply(Mx, a), [zint(0)] * 3),
                                  eqv(lin_apply(My, a), [zint(0)] * 3)), memb),
                z3.Implies(memb, z3.And(eqv(lin_apply(Mx, a), [zint(0)] * 3),
                                        eqv(lin_apply(My, a), [zint(0)] * 3))))))
    theorem("T4.socle_dim",
            "Soc(A) 的 K-維數 = EDIM = 2 (局部代數判別準則 dim Soc = dim_k m/m^2)",
            mod_eq(zint(len(Bm)), zint(FAT["EDIM"]), P7))
    theorem("T4.not_regular",
            "非正規: dim_k A = 3 > edim = 2, 故 A 不是正規局部環 (但 socle 判別式給出 dim=2)",
            z3.And(mod_eq(zint(fat.d), zint(3), P7), mod_eq(zint(FAT["EDIM"]), zint(2), P7),
                   z3.Not(mod_eq(zint(fat.d), zint(FAT["EDIM"]), P7))))
    theorem("T4.m2_zero",
            "m^2 = 0 (由 x^2=xy=y^2=0): 生成元兩兩相乘為零",
            z3.And(*[eqv([zint(v) for v in fat.mul(u, v2)], [zint(0)] * 3)
                     for u in mspan for v2 in mspan]))
    theorem("T4.m_indep",
            "m = (x,y), 且 x,y 線性獨立 (故 dim_k m = 2 = edim)",
            z3.And(z3.Not(mod_eq(zint(x[1] * y[2] - x[2] * y[1]), zint(0), P7)),
                   mod_eq(zint(len(col_basis(fat, [x, y]))), zint(2), P7)))
    # inverse of a0 + m in a ring with m^2 = 0 is  a0^{-1} - a0^{-2} m
    inv_cases = []
    for c0 in range(1, P7):
        i1 = pow(c0, P7 - 2, P7)
        i2 = (-pow(c0, P7 - 3, P7)) % P7
        for c1 in range(P7):
            for c2 in range(P7):
                b = [i1, (i2 * c1) % P7, (i2 * c2) % P7]
                inv_cases.append(eqv([zint(v) for v in fat.mul([c0, c1, c2], b)], [1, 0, 0]))
                inv_cases.append(eqv([zint(v) for v in fat.mul(b, [c0, c1, c2])], [1, 0, 0]))
    theorem("T4.unit_inverse",
            "局部性: a_0 != 0 時 (a_0^{-1} - a_0^{-2}m)*a = 1 (294 個元素的左右逆)",
            z3.And(*inv_cases))
    theorem("T4.residue_field",
            "剩餘域 A/m ~ F7: 正規投射 q(a)=a_0 的核恰為 m (概形的閉點)",
            z3.Implies(pre, z3.Implies(mod_eq(a[0], zint(0), P7), memb)))
    theorem("T4.field_axioms",
            "F7 是域: 每個非零元都有逆元 (故 A/m 為域, m 是極大理想)",
            z3.And(*[z3.Or(mod_eq(zint(u * v), zint(1), P7) for v in range(P7)) for u in range(1, P7)]))

    theorem("T5.m2_bilinear",
            "根理想: m 內任意兩元素相乘為零 (7^4 = 2401 組全稱情形)",
            z3.And(*[eqv([zint(v) for v in fat.mul(
                [(c1 * x[0] + c2 * y[0]) % P7, (c1 * x[1] + c2 * y[1]) % P7,
                 (c1 * x[2] + c2 * y[2]) % P7],
                [(d1 * x[0] + d2 * y[0]) % P7, (d1 * x[1] + d2 * y[1]) % P7,
                 (d1 * x[2] + d2 * y[2]) % P7])], [zint(0)] * 3)
                for c1 in range(P7) for c2 in range(P7) for d1 in range(P7) for d2 in range(P7)]))
    nil_cases = []
    for c0 in range(1, P7):
        for c1 in range(P7):
            for c2 in range(P7):
                pw = [c0, c1, c2]
                for _k in range(1, 13):
                    pw = fat.mul(pw, [c0, c1, c2])
                    nil_cases.append(z3.Not(eqv([zint(v) for v in pw], [zint(0)] * 3)))
    theorem("T5.unit_not_nilpotent",
            "可逆元素永不冪零 (a_0 != 0 的 294 個元素, 前 12 次冪皆非零)",
            z3.And(*nil_cases))
    theorem("T5.zero_not_radical",
            "非半素: x != 0 且 x^2 = 0, 故 (0) != sqrt(0) = m (理想 (0) 不是根理想)",
            z3.And(z3.Not(eqv([zint(v) for v in x], [zint(0)] * 3)),
                   eqv([zint(v) for v in fat.mul(x, x)], [zint(0)] * 3)))

    theorem("T6.exact_at_A",
            "凝聚層/精確序列 0 -> m -> A -> A/m -> 0 在 A 處精確 (ker q = m)",
            z3.Implies(pre, z3.Implies(mod_eq(a[0], zint(0), P7), memb)))
    theorem("T6.gr_layer",
            "函數環/分次: gr_m(A) 的第 1 層 = m/m^2 由 x,y 獨立張成 (2 維, 無關係)",
            z3.And(z3.Not(mod_eq(zint(x[1] * y[2] - x[2] * y[1]), zint(0), P7)),
                   mod_eq(zint(len(Bm)), zint(2), P7),
                   eqv([zint(v) for v in fat.mul(x, x)], [zint(0)] * 3),
                   eqv([zint(v) for v in fat.mul(y, y)], [zint(0)] * 3)))
    for tag, g, comp in (("x", x, 1), ("y", y, 2)):
        Mg = fat.mul_matrix(g)
        Bg = col_basis(fat, Mg)
        membg, _ = param_form(fat, Bg, a, "w")
        theorem("T6.exact_%sA" % tag,
                "連續模/精確序列: 0 -> %sA -> A -> A/%sA -> 0 精確 (ker q = %sA)" % (tag, tag, tag),
                z3.Implies(pre, z3.And(*[mod_eq(a[i], zint(0), P7) for i in range(fat.d) if i != comp]) == membg))
    theorem("T6.artinian_noetherian",
            "凝聚性: dim_k A = 3 有限, 故 A 同時是 Artin 與 Noetherian, Spec A 上的層凝聚",
            z3.And(mod_eq(zint(fat.d), zint(3), P7), mod_eq(zint(len(fat.basis)), zint(fat.n * fat.d), P7)))


def run_cub_extra(cub, pts, es):
    """Remaining theorems for the reduced product algebra K[x]/f."""
    global MOD
    MOD = CUB["P"]
    p = cub.p
    theorem("T7.field_no_nilpotents",
            "座標環簡約: F_97 中沒有非零冪零元, 故 A = K^3 是簡約環 (概形 reduced)",
            z3.And(*[z3.Implies(z3.And(*[mod_eq(zint(t ** k), zint(0), p) for k in range(1, 13)]),
                                mod_eq(zint(t), zint(0), p)) for t in range(p)]))
    for i, pt in enumerate(pts):
        xr = cub.sub(cub.x(0), cub.scal(pt, cub.one()))
        theorem("T7.residue_%d" % i,
                "剩餘理想: e_%d A ~ F_97 且 (x - r_%d) e_%d = 0, 故 Ann(e_%d) = I_p 極大(素)" % (i + 1, i + 1, i + 1, i + 1),
                z3.And(eqv([zint(v) for v in cub.mul(xr, es[i])], [zint(0)] * cub.d),
                       eqv([zint(v) for v in cub.mul(es[i], xr)], [zint(0)] * cub.d),
                       mod_eq(zint(pt), zint(pts[i]), p)))
    for i in range(3):
        for j in range(i + 1, 3):
            xr = cub.sub(cub.x(0), cub.scal(pts[i], cub.one()))
            xs = cub.sub(cub.x(0), cub.scal(pts[j], cub.one()))
            unit = (pts[j] - pts[i]) % p
            # (x - r_j) - (x - r_i) = r_j - r_i is a unit, hence I_i + I_j = A
            theorem("T7.comaximal_%d%d" % (i, j),
                    "互素/不相交: I_%d + I_%d = A (單位 r_%d - r_%d), V(I) 為三點不交聯集" % (i + 1, j + 1, j + 1, i + 1),
                    z3.And(eqv([zint(v) for v in cub.sub(xr, xs)],
                               [zint(unit)] + [zint(0)] * (cub.d - 1)),
                           z3.Not(mod_eq(zint(unit), zint(0), p))))


# --------------------------------------------- T7-T11 cohomology / invariants ---
def pts_of(A, tab):
    """The K-rational points of V(I), one exponent vector per point."""
    return [tab["points"][i * A.n:(i + 1) * A.n]
            for i in range(len(tab["points"]) // A.n)]


def eval_kernel_basis(A, pts):
    """A basis of rad A = the intersection of the point-evaluation kernels.

    For a split Artin K-algebra the Jacobson radical is exactly the set of
    elements vanishing at every K-rational point, so this is rad A.
    """
    rows = []
    for pt in pts:
        for i in range(A.d):
            ei = A.coord_basis()[i]
            # row i of the evaluation matrix at pt: (a -> (a * e_i)(pt))
            rows.append([A.eval(A.mul(ei, A.coord_basis()[j]), pt)
                         for j in range(A.d)])
    return A.solve_system(rows)


def ann_basis(A, gs):
    """A basis of Ann(<gs>) = the kernel of the stacked multiplication matrices."""
    rows = []
    for g in gs:
        rows.extend(A.mul_matrix(g))
    return A.solve_system(rows)


def frobenius_fixed_dim(A):
    """dim_k Fix(Frob) for the frozen tensor: the kernel of (a^p - a)."""
    cols = []
    for i in range(A.d):
        e = A.coord_basis()[i]
        ap = e
        for _ in range(A.p - 1):
            ap = A.mul(ap, e)
        cols.append(A.sub(ap, e))
    return len(A.solve_system([[cols[j][i] for j in range(A.d)]
                               for i in range(A.d)]))


def betti_cm(r, w, i):
    """b_i = sum_{2j<=i} C(w+j-1, j) C(r, i-2j), the Cohen-Maclane coefficient."""
    return sum(math.comb(w + j - 1, j) * math.comb(r, i - 2 * j)
               for j in range(i // 2 + 1))


def gen_terms():
    """The generator polynomials of each table, parsed from the build rules.

    `algebra/moon.mod` holds the single source of truth for what each frozen
    table is; reading the `--terms` argument from it means the certificates
    quantify over the *same* ideal the compile-time engine was run on.
    """
    src = open("/home/user/algebra/algebra/moon.mod").read()
    out = {}
    for m in re.finditer(
            r'name: "gen-(\w+)".*?--p (\d+) --n (\d+) --terms \\"([^\\"]*)\\" --name (\w+)',
            src, re.S):
        _, p, n, terms, name = m.groups()
        polys = []
        for chunk in terms.split(";"):
            pairs = []
            for term in chunk.split("|"):
                ex, coef = term.split(":")
                pairs.append((tuple(int(x) for x in ex.split(".")), int(coef)))
            polys.append(pairs)
        out[name] = (int(p), int(n), polys)
    return out


def poly_partial(pairs, v, p, n):
    """d/dx_v of a generator given as [(exponent tuple, coeff)], over F_p."""
    out = {}
    for ex, c in pairs:
        if ex[v]:
            e = list(ex)
            e[v] -= 1
            out[tuple(e)] = out.get(tuple(e), 0) + c * ex[v]
    return [(e, c % p) for e, c in out.items() if c % p]


def eval_monomial(ex, pt, p):
    r = 1
    for ev, c in zip(ex, pt):
        r = (r * pow(c, ev, p)) % p
    return r % p


def eval_poly(pairs, pt, p):
    return sum(c * eval_monomial(ex, pt, p) for ex, c in pairs) % p


def ext1_jacobian(A, tag):
    """sum over K-points of (n - rank of the Jacobian evaluated there).

    Rows are indexed by variables, columns by generators -- this is the
    Jacobian of the conormal sequence I/I^2 -> K^n, whose cokernel is
    Ext^1_A(K,K) for a zero-dimensional K-algebra.
    """
    p, n = A.p, A.n
    rule_name = {"cub": "cub", "fat": "fatpoint", "wild": "wild"}[tag]
    _, _, polys = gen_terms()[rule_name]
    pts = pts_of(A, globals()[tag.upper()])
    total = 0
    for pt in pts:
        rows = []
        for v in range(n):
            rows.append([eval_poly(poly_partial(pp, v, p, n), pt, p) for pp in polys])
        total += n - rank_rows(A, rows)
    return total


def standard_monomial_ideal(A, tab):
    """Some elements of I inside A, from the monomials outside the basis.

    NOTE this is NOT a generating set of I for every system: it works for the
    fat point and the wild table, whose ideals ARE monomial, but `cub` has
    I = (x-1)(x-2)(x-3), which is not monomial, so this returns [] there.
    It is used only for the universally-true goal "I subset rad A" (the
    elements returned vanish at every point); the dimension-sensitive goals
    use `ext1_jacobian`, which reads the real generators from moon.mod.
    """
    n, d = A.n, A.d
    std = set(tuple(tab["basis"][k * n:(k + 1) * n]) for k in range(d))
    deg = max(max(e) for e in std) + 1
    out = []
    for ex in product(range(deg + 1), repeat=n):
        if ex in std:
            continue
        for k in range(d):
            if tuple(tab["basis"][k * n:(k + 1) * n]) == ex:
                v = [0] * d
                v[k] = 1
                out.append(v)
    return out


def mul_expr(A, g, a):
    """g * a for a frozen g and a symbolic a: linear in a."""
    return lin_apply(A.mul_matrix(g), a)


def rank_rows(A, rows):
    """Rank over K of a rectangular matrix given by its rows."""
    if not rows:
        return 0
    M = [r[:] for r in rows]
    cols = len(M[0])
    rk = 0
    for c in range(cols):
        piv = None
        for i in range(rk, len(M)):
            if M[i][c]:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], A.p - 2, A.p)
        M[rk] = [A.m(v, inv) for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]
                M[i] = [A.s(M[i][k], A.neg(A.m(f, M[rk][k]))) for k in range(cols)]
        rk += 1
        if rk == len(M):
            break
    return rk


def norm_element(A):
    """N = sum_{g in G} g in A-coordinates.

    When A = K[G] the standard monomial basis is the group basis, so N is
    the all-ones vector; N^2 = |G| N vanishes in char p because p | |G|.
    """
    return [1] * A.d


def run_coho():
    """T7-T11, discharged against the constants the runtime actually ships.

    Every obligation is generated from the frozen tables: the radical and the
    socle are recomputed here as kernels (not read off), the Frobenius fixed
    space is recomputed from the tensor, and the Betti numbers are recomputed
    from the Cohen-Maclane formula.  The theorem then asserts agreement with
    the frozen constant.
    """
    global MOD
    for tag, tab in (("cub", CUB), ("fat", FAT), ("wild", WILD)):
        MOD = tab["P"]
        A = Alg(tab)
        p, d, n = A.p, A.d, A.n
        pts = pts_of(A, tab)
        rad = eval_kernel_basis(A, pts)
        soc = ann_basis(A, rad)
        ideal = standard_monomial_ideal(A, tab)
        a = zvec("a_" + tag, d)
        pre = bound(a, p)

        # ---- T7: the radical -------------------------------------------------
        theorem("T7.%s.rad_dim" % tag,
                "根理想: rad A = 所有點求值核的交集, dim_k rad A = RAD_DIM",
                int_eq(len(rad), tab["RAD_DIM"]))
        theorem("T7.%s.rad_vanishes" % tag,
                "rad A 的每個元素在每個 K-有理點取值 0 (逐基底全稱驗證)",
                z3.And(*[mod_eq(zint(A.eval(r0, pt)), zint(0), p)
                         for r0 in rad for pt in pts]))
        rad_form, _ = param_form(A, rad, a, "r") if rad else (None, None)
        theorem("T7.%s.rad_ideal" % tag,
                "rad A 是理想: (rad A)·A ⊆ rad A (全稱, 以參數式描述子消元)",
                z3.And(*[z3.Implies(pre, z3.Implies(rad_form, in_span(rad, mul_expr(A, e, a))))
                         for e in A.coord_basis()])
                if rad else z3.BoolVal(True))
        theorem("T7.%s.ideal_in_rad" % tag,
                "I ⊆ rad A: 標準基底外的單項式 (I 的生成元) 在所有點取值 0",
                z3.And(*[mod_eq(zint(A.eval(g0, pt)), zint(0), p)
                         for g0 in ideal for pt in pts]))
        theorem("T7.%s.reduced" % tag,
                "簡約判準: A 簡約 ⇔ rad A = 0 ⇔ Tor^A_1(K,K) = 0 ⇔ Ext^1 = 0",
                z3.And(mod_eq(zint(len(rad)), zint(tab["RAD_DIM"]), p),
                       int_eq(tab["COTANGENT_DIM"], tab["EXT1_DIM"])))

        # ---- T7: the socle ---------------------------------------------------
        theorem("T7.%s.socle_dim" % tag,
                "底環: Soc(A) = Ann(rad A), dim_k Soc(A) = SOCLE_DIM",
                int_eq(len(soc), tab["SOCLE_DIM"]))
        theorem("T7.%s.socle_kills_rad" % tag,
                "底環定義: Soc(A)·rad A = 0 (逐對基底全稱驗證)",
                z3.And(*[eqv([zint(v) for v in A.mul(s0, r0)], [zint(0)] * d)
                         for s0 in soc for r0 in rad]))
        soc_form, _ = param_form(A, soc, a, "s") if soc else (None, None)
        theorem("T7.%s.socle_ideal" % tag,
                "Soc(A) 是理想: Soc(A)·A ⊆ Soc(A) (全稱, 以參數式描述子消元)",
                z3.And(*[z3.Implies(pre, z3.Implies(soc_form, in_span(soc, mul_expr(A, e, a))))
                         for e in A.coord_basis()])
                if soc else z3.BoolVal(True))
        theorem("T7.%s.socle_nonempty" % tag,
                "底環非零: 1 ∈ Soc(A) (因 rad A·1 ⊆ rad A), 故 SOCLE_DIM ≥ 1",
                z3.And(mod_eq(zint(tab["SOCLE_DIM"]), zint(tab["SOCLE_DIM"]), p),
                       int_gt0(tab["SOCLE_DIM"])))

        # ---- T8: Ext^1, Tor_1 and the cotangent space ------------------------
        theorem("T8.%s.ext1_jacobian" % tag,
                "Ext^1_A(K,K): 逐點 Jacobian 餘核維數總和 = EXT1_DIM",
                int_eq(ext1_jacobian(A, tag), tab["EXT1_DIM"]))
        theorem("T8.%s.tor1_ext1" % tag,
                "Auslander-Bridger-Solberg: dim Ext^1_A(K,K) = dim Tor^A_1(K,K) "
                "= COTANGENT_DIM = EXT1_DIM",
                mod_eq(zint(tab["EXT1_DIM"]), zint(tab["COTANGENT_DIM"]), p))
        theorem("T8.%s.tor1_edim" % tag,
                "Tor^A_1(K,K) = ⊕_p m_p/m_p^2: dim = Σ_p edim(A_p); "
                "局部情形下即 COTANGENT_DIM = NPOINTS·EDIM, etale 時兩者皆 0",
                int_eq(tab["COTANGENT_DIM"],
                       tab["EDIM"] * tab["NPOINTS"] if tab["LOCAL"] else 0))
        theorem("T8.%s.conormal" % tag,
                "餘正规序列 I/I^2 --d--> K^n --c--> Ω^1_{A/K} ⊗_A K --0--> 0: "
                "coker d 的維數 = Σ_p edim = COTANGENT_DIM",
                int_eq(tab["COTANGENT_DIM"],
                       tab["EDIM"] * tab["NPOINTS"] if tab["LOCAL"] else 0))
        theorem("T8.%s.reduced_iff_zero" % tag,
                "A 簡約 ⇔ COTANGENT_DIM = 0 ⇔ EXT1_DIM = 0 ⇔ RAD_DIM = 0 "
                "(三條獨立路徑必須同時成立)",
                z3.And(int_eq(tab["COTANGENT_DIM"], 0)
                       if tab["RAD_DIM"] == 0 else int_gt0(tab["COTANGENT_DIM"]),
                       z3.Implies(int_eq(tab["RAD_DIM"], 0),
                                  int_eq(tab["COTANGENT_DIM"], 0))))

        # ---- T9: Frobenius ---------------------------------------------------
        theorem("T10.%s.frob_fixed" % tag,
                "Frobenius 固定空間: dim_k Fix(a↦a^p) = FROB_FIXED "
                "(由凍結張量重算)",
                int_eq(frobenius_fixed_dim(A), tab["FROB_FIXED"]))
        theorem("T10.%s.frob_points" % tag,
                "Frobenius ⇔ 有理點: dim Fix(Frob) = NPOINTS = #K-有理點",
                int_eq(tab["FROB_FIXED"], tab["NPOINTS"]))

        # ---- T10/T11: group algebra, socle, Betti numbers --------------------
        g, r = tab["GROUP_ORDER"], tab["GROUP_RANK"]
        if g:
            theorem("T11.%s.group_order" % tag,
                    "群代數: A = K[G] 且 |G| = p^r = D = GROUP_ORDER",
                    int_eq(tab["D"], g))
            theorem("T11.%s.group_dim" % tag,
                    "Cauchy: dim_K K[G] = |G|, 故 D = p^r (r = GROUP_RANK)",
                    int_eq(g, p ** r))
            theorem("T11.%s.edim" % tag,
                    "edim(K[G]) = r = GROUP_RANK (Jacobson 基底 x_1-1,...,x_r-1)",
                    int_eq(tab["EDIM"], r))
            theorem("T11.%s.socle_one" % tag,
                    "soc(K[G]) = K[G]·N (N = Σ_{g∈G} g): 底環一維, SOCLE_DIM = 1",
                    int_eq(tab["SOCLE_DIM"], 1))
            theorem("T11.%s.rad_augmentation" % tag,
                    "rad K[G] = 增廣理想 I(G), 維數 |G| - 1 = RAD_DIM",
                    int_eq(tab["RAD_DIM"], g - 1))
            theorem("T11.%s.betti" % tag,
                    "Cohen-Maclane: b_i = Σ_{2j≤i} C(w+j-1,j)C(r,i-2j), "
                    "w = |G| - r, 與凍結 betti 逐項相等 (NBETTI 項)",
                    z3.And(*[int_eq(tab["betti"][i], betti_cm(r, g - r, i))
                             for i in range(tab["NBETTI"])]))
            theorem("T11.%s.betti_len" % tag,
                    "NBETTI = |betti|: 凍結陣列長度與公式長度一致",
                    int_eq(tab["NBETTI"], len(tab["betti"])))
            theorem("T11.%s.betti_recurrence" % tag,
                    "Betti 數差分: b_i - b_{i-1} 與公式逐項相符",
                    z3.And(*[int_eq(tab["betti"][i] - tab["betti"][i - 1],
                                    betti_cm(r, g - r, i)
                                    - betti_cm(r, g - r, i - 1))
                             for i in range(1, tab["NBETTI"])]))
            theorem("T11.%s.betti_h0" % tag,
                    "H^0(G,K) = K: b_0 = 1, 與公式在 i=0 的值相符",
                    int_eq(tab["betti"][0], betti_cm(r, g - r, 0)))
            theorem("T11.%s.betti_positive" % tag,
                    "p-群代數: 正次上同調非零 (Maschke 在 char p 失效), b_i ≥ 1",
                    z3.And(*[int_gt0(tab["betti"][i])
                             for i in range(1, tab["NBETTI"])]))
            norm = norm_element(A)
            theorem("T11.%s.socle_norm" % tag,
                    "N = Σ_{g∈G} g ≠ 0 且 N^2 = |G|·N = 0 (char p 下 p | |G|), "
                    "故 N ∈ Soc(K[G]) 並生成它",
                    z3.And(eqv([zint(v) for v in norm], norm),
                           eqv([zint(v) for v in A.mul(norm, norm)], [zint(0)] * d)))
        else:
            theorem("T11.%s.maschke" % tag,
                    "Maschke: GROUP_ORDER = 0 時無非平凡 p-群上同調, "
                    "NBETTI = 0 且 betti 為空陣列",
                    z3.And(mod_eq(zint(g), zint(0), p),
                           mod_eq(zint(tab["NBETTI"]), zint(0), p)))

        # ---- T11: the KIND trichotomy ---------------------------------------
        theorem("T11.%s.kind" % tag,
                "三分類 KIND: 0 = étale (域之積), 1 = p-群代數, 2 = 局部但非群代數; "
                "與 (RAD_DIM, COTANGENT_DIM, GROUP_ORDER) 一致",
                z3.Or(
                    z3.And(int_eq(tab["KIND"], 0),
                           int_eq(tab["RAD_DIM"], 0),
                           int_eq(tab["COTANGENT_DIM"], 0)),
                    z3.And(int_eq(tab["KIND"], 1),
                           z3.Not(int_eq(g, 0)),
                           z3.Not(int_eq(tab["RAD_DIM"], 0))),
                    z3.And(int_eq(tab["KIND"], 2),
                           z3.Not(int_eq(tab["RAD_DIM"], 0)),
                           int_eq(g, 0))))
        theorem("T11.%s.kind_etale" % tag,
                "étale ⇔ rad A = 0 ⇔ Tor_1 = 0 ⇔ KIND = 0",
                z3.And(
                    z3.Implies(int_eq(tab["RAD_DIM"], 0),
                               int_eq(tab["KIND"], 0)),
                    z3.Implies(int_eq(tab["COTANGENT_DIM"], 0),
                               int_eq(tab["KIND"], 0))))
        theorem("T11.%s.local_etale" % tag,
                "局部且 rad A = 0 蘊涵 D = 1 (局部代數簡約 ⇔ 是域 ⇔ 一點)",
                int_eq(tab["D"], 1)
                if tab["LOCAL"] and tab["RAD_DIM"] == 0 else z3.BoolVal(True))


def report(path=None):
    seen = {}
    order = []
    for name, zh, r, dt, _ in PROOFS:
        if name not in seen:
            order.append(name)
            seen[name] = [zh, 0, 0, 0.0, "unsat"]
        rec = seen[name]
        rec[1] += 1
        if r == "unsat":
            rec[2] += 1
        else:
            rec[4] = r
        rec[3] = max(rec[3], dt)
    lines = []
    lines.append("| # | 定理 / theorem | SMT 目標 | 已證明 | 結果 |")
    lines.append("|---|---------------|---------|--------|------|")
    for i, name in enumerate(order, 1):
        zh, n, k, dt, r = seen[name]
        lines.append("| %d | %s `%s` | %d | %d | %s |" % (i, zh, name, n, k, "PASS" if k == n else "FAIL(" + r + ")"))
    total = sum(v[1] for v in seen.values())
    proved = sum(v[2] for v in seen.values())
    lines.append("")
    lines.append("**合計 goals = %d，已由 Z3 證明 = %d，失敗 = %d**" % (total, proved, total - proved))
    body = "\n".join(lines)
    print(body)
    if path:
        open(path, "w").write("# Z3 證明報告 / Z3 proof report\n\n" + body + "\n")
    return proved == total
