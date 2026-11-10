"""Exact branch-and-bound for the program with the inequalities (*) at a fixed budget lambda.

Program (rows built by rows_star.py; the row L <= 1 becomes L <= lambda):
  variables  s1..s6, s (s in a,b,c), Fa, Fb, Fc, D  (25 non-negative reals)
  root rows  (B1)-(B3) linearised + ordering (5.1)
  disjunctions  (B4) for every (I_a, I_b, I_c) (two branches)
                (*)  for all 24 ordered (A,pA,B,pB) (five branches)

Output: a JSON tree with the fields "lambda",
"Dstar", "attained" and the exact feasible point.  Every leaf carries exact
rational Farkas multipliers y with (y^T A)_D = 1, (y^T A)_v >= 0, y^T b = bound.

Floating point (scipy/HiGHS) is used only to *find* bases; every certificate is
then re-solved and verified in fractions.Fraction before being written.

Run:
    python3 bb_lambda.py 0.70 0.75 ... 1.10            # program with the 24 inequalities (*)
    python3 bb_lambda.py --no-tl 0.70 ... 1.10        # BLT v2 inputs only, writes cert_base_*.json
"""
from fractions import Fraction as F
from itertools import permutations, product
import json
import sys
import time

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import rows_star as cf  # noqa: E402  (row formulas: _build_v2_base_rows, _cond_to_rows)

ZERO = F(0)
N = cf.N_VARS
D_IDX = cf.D_IDX
IDX = cf.IDX
R6 = range(1, 7)
SUBSETS = [tuple(i for i in R6 if m >> (i - 1) & 1) for m in range(64)]
TL_KEYS = [(A, pA, B, pB) for A, B in permutations("abc", 2) for pA in ((2, 3), (3, 4)) for pB in ((2, 3), (3, 4))]


def base_rows(lam):
    rows = cf._build_v2_base_rows()
    r0, b0 = rows[0]
    assert b0 == 1 and r0[IDX["a"]] == 1 and r0[IDX["b"]] == 1 and r0[IDX["c"]] == 1
    rows[0] = (r0, F(lam))
    return rows


# ----------------------------------------------------------------- exact linear algebra
def solve_rational(A, b):
    """Solve A x = b over Fraction (A: list of rows). Free variables -> 0. None if inconsistent."""
    m = len(A)
    n = len(A[0]) if m else 0
    M = [list(A[i]) + [b[i]] for i in range(m)]
    piv_cols = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, m):
            if M[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][c]
        M[r] = [v / pv for v in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        piv_cols.append(c)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        if M[i][n] != 0:
            return None
    x = [ZERO] * n
    for i, c in enumerate(piv_cols):
        x[c] = M[i][n]
    return x


def verify_farkas(rows, y):
    """Return exact bound if y is a valid Farkas multiplier for 'D <= bound', else None."""
    if not y or any(v <= 0 for v in y.values()):
        return None
    for j in range(N):
        s = sum(v * rows[i][0][j] for i, v in y.items())
        if j == D_IDX:
            if s != 1:
                return None
        elif s < 0:
            return None
    return sum(v * rows[i][1] for i, v in y.items())


def exact_simplex_min(Meq, req, cost):
    """Exact two-phase simplex (Bland) for  min cost.y  s.t.  Meq y = req, y >= 0.
    Returns (y list, value) or (None, None) if infeasible.  Small dense tableau over Fraction."""
    m = len(Meq)
    n = len(Meq[0]) if m else len(cost)
    # make req >= 0
    M = [list(r) for r in Meq]
    rq = list(req)
    for i in range(m):
        if rq[i] < 0:
            M[i] = [-v for v in M[i]]
            rq[i] = -rq[i]
    # tableau with artificials n..n+m-1
    T = [M[i] + [F(1) if k == i else ZERO for k in range(m)] + [rq[i]] for i in range(m)]
    basis = [n + i for i in range(m)]

    def pivot(r, c):
        pv = T[r][c]
        T[r] = [v / pv for v in T[r]]
        for i in range(m):
            if i != r and T[i][c] != 0:
                f = T[i][c]
                T[i] = [vi - f * vr for vi, vr in zip(T[i], T[r])]
        basis[r] = c

    def run(obj, allowed):
        # obj: list of length ncols (reduced costs computed from obj over basis)
        while True:
            # reduced costs
            red = list(obj)
            for i in range(m):
                cb = obj[basis[i]]
                if cb != 0:
                    red = [rj - cb * tij for rj, tij in zip(red, T[i])]
            enter = None
            for j in allowed:
                if red[j] < 0:
                    enter = j
                    break
            if enter is None:
                return
            ratio = None
            leave = None
            for i in range(m):
                if T[i][enter] > 0:
                    rt = T[i][-1] / T[i][enter]
                    if ratio is None or rt < ratio or (rt == ratio and basis[i] < basis[leave]):
                        ratio, leave = rt, i
            if leave is None:
                raise RuntimeError("unbounded")
            pivot(leave, enter)

    ncols = n + m
    phase1 = [ZERO] * n + [F(1)] * m + [ZERO]
    run(phase1, range(ncols))
    if any(T[i][-1] != 0 and basis[i] >= n for i in range(m)):
        return None, None
    # drive artificials out of basis where possible
    for i in range(m):
        if basis[i] >= n:
            for j in range(n):
                if T[i][j] != 0:
                    pivot(i, j)
                    break
    phase2 = list(cost) + [ZERO] * m + [ZERO]
    run(phase2, range(n))
    y = [ZERO] * n
    for i in range(m):
        if basis[i] < n:
            y[basis[i]] = T[i][-1]
    return y, sum(c * v for c, v in zip(cost, y))


def exact_dual(rows, xf, yf, tol=1e-9):
    """Exactify a float dual solution.  Restrict to rows S (float support / active rows) and impose
    (y^T A)_v = 0 on the primal support T, (y^T A)_D = 1; solve this small LP exactly (minimise y^T b).
    Fallback: the full dual LP  min b.y  s.t. A^T y >= e_D, y >= 0  solved exactly."""
    m = len(rows)
    Af = np.array([[float(c) for c in r] for r, _ in rows])
    bf = np.array([float(b) for _, b in rows])
    slack = bf - Af @ xf
    T = [v for v in range(N) if xf[v] > tol or v == D_IDX]
    # fast path: direct rational solve on the float support (non-degenerate case)
    S = [i for i in range(m) if yf[i] > tol]
    if S:
        sol = solve_rational([[rows[i][0][v] for i in S] for v in T], [F(1) if v == D_IDX else ZERO for v in T])
        if sol is not None:
            y = {i: v for i, v in zip(S, sol) if v != 0}
            bd = verify_farkas(rows, y)
            if bd is not None:
                return y, bd
    tried = set()
    for S in (
        [i for i in range(m) if yf[i] > tol],
        [i for i in range(m) if yf[i] > 1e-12 or abs(slack[i]) < 1e-9],
        [i for i in range(m) if abs(slack[i]) < 1e-7],
    ):
        key = tuple(S)
        if not S or key in tried:
            continue
        tried.add(key)
        Meq = [[rows[i][0][v] for i in S] for v in T]
        req = [F(1) if v == D_IDX else ZERO for v in T]
        cost = [rows[i][1] for i in S]
        sol, _ = exact_simplex_min(Meq, req, cost)
        if sol is None:
            continue
        y = {i: v for i, v in zip(S, sol) if v != 0}
        bd = verify_farkas(rows, y)
        if bd is not None:
            return y, bd
    # full dual LP with slack columns:  A^T y - s = e_D
    Meq = [[rows[i][0][v] for i in range(m)] + [-F(1) if k == v else ZERO for k in range(N)] for v in range(N)]
    req = [F(1) if v == D_IDX else ZERO for v in range(N)]
    cost = [rows[i][1] for i in range(m)] + [ZERO] * N
    sol, _ = exact_simplex_min(Meq, req, cost)
    if sol is None:
        return None, None
    y = {i: v for i, v in enumerate(sol[:m]) if v != 0}
    bd = verify_farkas(rows, y)
    if bd is not None:
        return y, bd
    return None, None


def exact_primal(rows, xf, tol=1e-9):
    """Exactify a float primal vertex; return x (list of Fractions) if exactly feasible."""
    T = [v for v in range(N) if xf[v] > tol]
    Af = np.array([[float(c) for c in r] for r, _ in rows])
    bf = np.array([float(b) for _, b in rows])
    slack = bf - Af @ xf
    for tol_s in (tol, 1e-11, 1e-7):
        Ract = [i for i in range(len(rows)) if abs(slack[i]) < tol_s]
        A = [[rows[i][0][v] for v in T] for i in Ract]
        bvec = [rows[i][1] for i in Ract]
        sol = solve_rational(A, bvec)
        if sol is None:
            continue
        x = [ZERO] * N
        for v, s in zip(T, sol):
            x[v] = s
        if all(s >= 0 for s in x) and all(sum(r[j] * x[j] for j in range(N) if r[j] != 0) <= b for r, b in rows):
            return x
    return None


# ----------------------------------------------------------------- disjunction evaluation
def xdict(x):
    d = {}
    for s in "abc":
        for i in R6:
            d[s, i] = x[IDX[f"{s}{i}"]]
        d[s] = x[IDX[s]]
    d["D"] = x[D_IDX]
    return d


def geo_value_exact(xd, I, J, K):
    L = xd["a"] + xd["b"] + xd["c"]
    s0 = sum(xd["a", i] for i in I) + sum(xd["b", i] for i in J) + sum(xd["c", i] for i in K)
    s1 = sum((i - 1) * xd["a", i] for i in I) + sum((i - 1) * xd["b", i] for i in J) + sum((i - 1) * xd["c", i] for i in K)
    return max(L - s0, L - 1 + s1)


def tl_value_exact(xd, A, pA, B, pB):
    C = ({"a", "b", "c"} - {A, B}).pop()
    p, q = xd[A, pA[0]], xd[A, pA[1]]
    r, s = xd[B, pB[0]], xd[B, pB[1]]
    w = sum(i * xd[B, i] for i in R6 if i not in pB) + 7 * (xd[B] - sum(xd[B, i] for i in R6))
    kappa = p + q + (max(ZERO, 2 * p - w) + max(ZERO, 2 * q - w)) / 2
    outer = xd[A] - p - q + xd[B] - r - s
    return outer + max(xd[C], (xd[C] + min(r + s, 2 * r, 2 * s) + kappa) / 2)


def most_violated_geo_float(xf):
    """Return (violation, (I,J,K)) of the (B4) disjunction most violated at xf (float)."""
    L = xf[IDX["a"]] + xf[IDX["b"]] + xf[IDX["c"]]
    D = xf[D_IDX]
    s0 = {}
    s1 = {}
    for s in "abc":
        vals = np.array([xf[IDX[f"{s}{i}"]] for i in R6])
        s0[s] = np.array([sum(vals[i - 1] for i in I) for I in SUBSETS])
        s1[s] = np.array([sum((i - 1) * vals[i - 1] for i in I) for I in SUBSETS])
    S0 = s0["a"][:, None, None] + s0["b"][None, :, None] + s0["c"][None, None, :]
    S1 = s1["a"][:, None, None] + s1["b"][None, :, None] + s1["c"][None, None, :]
    val = np.maximum(L - S0, L - 1 + S1)
    k = int(np.argmin(val))
    ia, ib, ic = np.unravel_index(k, val.shape)
    return D - float(val[ia, ib, ic]), (SUBSETS[ia], SUBSETS[ib], SUBSETS[ic])


def top_violated_geo_float(xf, k, tol=1e-9):
    """Up to k distinct (B4) disjunctions violated at xf (both branches fail), most violated first."""
    L = xf[IDX["a"]] + xf[IDX["b"]] + xf[IDX["c"]]
    D = xf[D_IDX]
    s0 = {}
    s1 = {}
    for s in "abc":
        vals = np.array([xf[IDX[f"{s}{i}"]] for i in R6])
        s0[s] = np.array([sum(vals[i - 1] for i in I) for I in SUBSETS])
        s1[s] = np.array([sum((i - 1) * vals[i - 1] for i in I) for I in SUBSETS])
    S0 = s0["a"][:, None, None] + s0["b"][None, :, None] + s0["c"][None, None, :]
    S1 = s1["a"][:, None, None] + s1["b"][None, :, None] + s1["c"][None, None, :]
    val = np.maximum(L - S0, L - 1 + S1).ravel()
    idx = np.argsort(val)[: max(k, 1)]
    out = []
    for kk in idx:
        if D - val[kk] <= tol:
            break
        ia, ib, ic = np.unravel_index(int(kk), (64, 64, 64))
        out.append(("geo", SUBSETS[ia], SUBSETS[ib], SUBSETS[ic]))
    return out


def top_violated_tl_float(xf, k, tol=1e-9):
    xd = {}
    for s in "abc":
        for i in R6:
            xd[s, i] = xf[IDX[f"{s}{i}"]]
        xd[s] = xf[IDX[s]]
    D = xf[D_IDX]
    out = []
    for A, pA, B, pB in TL_KEYS:
        C = ({"a", "b", "c"} - {A, B}).pop()
        p, q = xd[A, pA[0]], xd[A, pA[1]]
        r, s = xd[B, pB[0]], xd[B, pB[1]]
        w = sum(i * xd[B, i] for i in R6 if i not in pB) + 7 * (xd[B] - sum(xd[B, i] for i in R6))
        kappa = p + q + (max(0.0, 2 * p - w) + max(0.0, 2 * q - w)) / 2
        outer = xd[A] - p - q + xd[B] - r - s
        v = outer + max(xd[C], (xd[C] + min(r + s, 2 * r, 2 * s) + kappa) / 2)
        if D - v > tol:
            out.append((D - v, ("tl", A, pA, B, pB)))
    out.sort(key=lambda t: -t[0])
    return [c for _, c in out[:k]]


def most_violated_tl_float(xf):
    xd = {}
    for s in "abc":
        for i in R6:
            xd[s, i] = xf[IDX[f"{s}{i}"]]
        xd[s] = xf[IDX[s]]
    D = xf[D_IDX]
    best = None
    for A, pA, B, pB in TL_KEYS:
        C = ({"a", "b", "c"} - {A, B}).pop()
        p, q = xd[A, pA[0]], xd[A, pA[1]]
        r, s = xd[B, pB[0]], xd[B, pB[1]]
        w = sum(i * xd[B, i] for i in R6 if i not in pB) + 7 * (xd[B] - sum(xd[B, i] for i in R6))
        kappa = p + q + (max(0.0, 2 * p - w) + max(0.0, 2 * q - w)) / 2
        outer = xd[A] - p - q + xd[B] - r - s
        v = outer + max(xd[C], (xd[C] + min(r + s, 2 * r, 2 * s) + kappa) / 2)
        if best is None or D - v > best[0]:
            best = (D - v, (A, pA, B, pB))
    return best


def all_disjunctions_hold_exact(x, use_tl=True):
    """Exact check of every (B4) and every (*) at the rational point x. Returns first violation or None."""
    xd = xdict(x)
    D = xd["D"]
    for key in (TL_KEYS if use_tl else []):
        if tl_value_exact(xd, *key) < D:
            return ("tl",) + key
    # (B4): minimise max(L - s0, L - 1 + s1) over 64^3 subsets exactly: do it per branch via floats first
    xf = np.array([float(v) for v in x])
    viol, (I, J, K) = most_violated_geo_float(xf)
    if geo_value_exact(xd, I, J, K) < D:
        return ("geo", I, J, K)
    if viol > -1e-9:  # float says near-tight: scan exactly all 2^18 to be safe
        L = xd["a"] + xd["b"] + xd["c"]
        per = {}
        for s in "abc":
            per[s] = [(sum(xd[s, i] for i in I), sum((i - 1) * xd[s, i] for i in I)) for I in SUBSETS]
        for ia, (a0, a1) in enumerate(per["a"]):
            for ib, (b0, b1) in enumerate(per["b"]):
                for ic, (c0, c1) in enumerate(per["c"]):
                    if max(L - a0 - b0 - c0, L - 1 + a1 + b1 + c1) < D:
                        return ("geo", SUBSETS[ia], SUBSETS[ib], SUBSETS[ic])
    return None


# ----------------------------------------------------------------- LP solve
def solve_lp(rows):
    A = np.array([[float(c) for c in r] for r, _ in rows])
    b = np.array([float(bb) for _, bb in rows])
    c = np.zeros(N)
    c[D_IDX] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * N, method="highs")
    if res.status == 2:
        return "infeasible", None, None
    if res.status != 0:
        raise RuntimeError(res.message)
    return "optimal", res.x, -res.ineqlin.marginals


def infeasibility_certificate(rows):
    """Exact y >= 0 with y^T A >= 0 (all columns) and y^T b < 0, via phase-1 LP  min t: A x - t <= b."""
    m = len(rows)
    A = np.array([[float(c) for c in r] + [-1.0] for r, _ in rows])
    b = np.array([float(bb) for _, bb in rows])
    c = np.zeros(N + 1)
    c[N] = 1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * (N + 1), method="highs")
    assert res.status == 0 and res.fun > 1e-9, res
    yf = -res.ineqlin.marginals
    xf = res.x
    for tol_y in (1e-9, 1e-11, 1e-7):
        S = [i for i in range(m) if yf[i] > tol_y]
        T = [v for v in range(N) if xf[v] > 1e-9]  # columns with y^T A_v = 0
        # unknowns y_S ; equations: sum y_i = 1 (normalisation), (y^T A)_v = 0 for v in T
        Asys = [[F(1)] * len(S)] + [[rows[i][0][v] for i in S] for v in T]
        bsys = [F(1)] + [ZERO] * len(T)
        sol = solve_rational(Asys, bsys)
        if sol is None:
            continue
        y = {i: v for i, v in zip(S, sol) if v != 0}
        if any(v <= 0 for v in y.values()):
            continue
        if all(sum(v * rows[i][0][j] for i, v in y.items()) >= 0 for j in range(N)):
            yb = sum(v * rows[i][1] for i, v in y.items())
            if yb < 0:
                return y, yb
    # exact fallback:  min b.y  s.t.  A^T y - s = 0, sum y = 1, y,s >= 0   (value < 0 iff infeasible)
    Meq = [[rows[i][0][v] for i in range(m)] + [-F(1) if k == v else ZERO for k in range(N)] for v in range(N)]
    Meq.append([F(1)] * m + [ZERO] * N)
    req = [ZERO] * N + [F(1)]
    cost = [rows[i][1] for i in range(m)] + [ZERO] * N
    sol, val = exact_simplex_min(Meq, req, cost)
    if sol is not None and val < 0:
        y = {i: v for i, v in enumerate(sol[:m]) if v != 0}
        return y, val
    return None, None


def trivial_cert(rows):
    """D <= a+b and a+b+c <= lambda  ->  D <= lambda. Rows 0 and the 'D - a - b <= 0' row."""
    i_triv = next(i for i, (r, b) in enumerate(rows) if r[D_IDX] == 1 and r[IDX["a"]] == -1 and r[IDX["b"]] == -1 and r[IDX["c"]] == 0)
    y = {0: F(1), i_triv: F(1)}
    bd = verify_farkas(rows, y)
    assert bd is not None
    return y, bd


# ----------------------------------------------------------------- branch and bound
class BB:
    def __init__(self, lam, use_tl=True):
        self.lam = F(lam)
        self.base = base_rows(self.lam)
        self.incumbent = ZERO  # x = 0 is feasible with D = 0
        self.incumbent_x = [ZERO] * N
        self.leaves = 0
        self.internal = 0
        self.lp_calls = 0
        self.max_depth = 0
        self.fail = []
        self.t0 = time.time()
        self.k_geo = 4  # strong-branching candidates
        self.k_tl = 4
        self.use_tl = use_tl  # False: BLT v2 inputs only (no (*) disjunctions)

    def rows_for(self, conds):
        rows = list(self.base)
        for c in conds:
            rows.extend(cf._cond_to_rows(c))
        return rows

    def leaf(self, y, bound):
        self.leaves += 1
        return {"type": "leaf", "y": {str(i): str(v) for i, v in sorted(y.items())}, "bound": str(bound)}

    def node(self, conds, depth):
        self.max_depth = max(self.max_depth, depth)
        rows = self.rows_for(conds)
        self.lp_calls += 1
        self.nodes = getattr(self, "nodes", 0) + 1
        if self.nodes % 50 == 0:
            print(f"   [progress] lp_calls={self.lp_calls} leaves={self.leaves} depth={depth} inc={float(self.incumbent):.6f} t={time.time()-self.t0:.0f}s", flush=True)
        status, xf, yf = solve_lp(rows)
        if status == "infeasible":
            y_inf, yb = infeasibility_certificate(rows)
            assert y_inf is not None, "could not exactify infeasibility certificate"
            y0, b0 = trivial_cert(rows)
            # y = (y0 + t*y_inf)/(1 + t*d), d = (y_inf^T A)_D >= 0.  bound = (b0 + t*yb)/(1 + t*d).
            # choose t so that bound = incumbent (<= D*):  t = (b0 - inc)/(inc*d - yb) > 0.
            inc = self.incumbent
            d = sum(v * rows[i][0][D_IDX] for i, v in y_inf.items())
            t = (b0 - inc) / (inc * d - yb)
            scale = 1 + t * d
            y = {i: v / scale for i, v in y0.items()}
            for i, v in y_inf.items():
                y[i] = y.get(i, ZERO) + t * v / scale
            bd = verify_farkas(rows, y)
            assert bd is not None and bd <= self.incumbent, (bd, self.incumbent)
            return self.leaf(y, bd)
        y, bound = exact_dual(rows, xf, yf)
        if y is None:
            self.fail.append(conds)
            import pickle
            with open(__file__.rsplit("/", 1)[0] + "/fail_dump.pkl", "wb") as f:
                pickle.dump({"rows": rows, "xf": xf, "yf": yf, "conds": conds}, f)
            raise RuntimeError(f"exactification failed at depth {depth}")
        if bound <= self.incumbent:
            return self.leaf(y, bound)
        geo_cands = top_violated_geo_float(xf, self.k_geo)
        tl_cands = top_violated_tl_float(xf, self.k_tl) if self.use_tl else []
        viol = None
        if not geo_cands and not tl_cands:
            # float point satisfies every disjunction: try to certify an exact feasible point
            x = exact_primal(rows, xf)
            if x is not None:
                v2 = all_disjunctions_hold_exact(x, self.use_tl)
                if v2 is None:
                    if x[D_IDX] > self.incumbent:
                        self.incumbent = x[D_IDX]
                        self.incumbent_x = x
                    if bound <= self.incumbent:
                        return self.leaf(y, bound)
                else:
                    viol = v2
            if viol is None:
                # fall back: branch on the least-slack disjunction (tolerance-free selection)
                vg, tg = most_violated_geo_float(xf)
                vt, tt = most_violated_tl_float(xf) if self.use_tl else (-1.0, None)
                viol = ("geo",) + tg if vg >= vt else ("tl",) + tt
        # strong branching among candidates
        if viol is None:
            best = None
            for cand in geo_cands + tl_cands:
                if cand[0] == "geo":
                    ccs = [conds + (cand + (br,),) for br in (0, 1)]
                else:
                    ccs = [conds + (cand + (br,),) for br in range(5)]
                vals = []
                for cc in ccs:
                    st, xx, _ = solve_lp(self.rows_for(cc))
                    self.lp_calls += 1
                    vals.append(xx[D_IDX] if st == "optimal" else -1.0)
                score = (max(vals), sum(v > float(self.incumbent) + 1e-9 for v in vals), len(vals))
                if best is None or score < best[0]:
                    best = (score, cand, ccs, vals)
            _, viol, children_conds, vals = best
        else:
            if viol[0] == "geo":
                children_conds = [conds + (viol + (br,),) for br in (0, 1)]
            else:
                children_conds = [conds + (viol + (br,),) for br in range(5)]
            vals = []
            for cc in children_conds:
                st, xx, _ = solve_lp(self.rows_for(cc))
                self.lp_calls += 1
                vals.append(xx[D_IDX] if st == "optimal" else -1.0)
        self.internal += 1
        if viol[0] == "geo":
            _, I, J, K = viol
            node = {"type": "geo", "I": list(I), "J": list(J), "K": list(K), "children": [None, None]}
        else:
            _, A, pA, B, pB = viol
            node = {"type": "tl", "A": A, "pA": list(pA), "B": B, "pB": list(pB), "children": [None] * 5}
        # best child first (finds strong incumbents early)
        for _, k in sorted((-v, k) for k, v in enumerate(vals)):
            node["children"][k] = self.node(children_conds[k], depth + 1)
        return node


def run(lam_str, use_tl=True):
    lam = F(lam_str)
    t0 = time.time()
    bb = BB(lam, use_tl)
    sys.setrecursionlimit(10000)
    tree = bb.node((), 0)
    tree_out = {
        "lambda": str(lam),
        "Dstar": str(bb.incumbent),
        "attained_point": {cf.VAR_NAMES[j]: str(v) for j, v in enumerate(bb.incumbent_x) if v != 0},
        "leaves": bb.leaves,
        "internal": bb.internal,
        "max_depth": bb.max_depth,
        "lp_calls": bb.lp_calls,
        "tree": tree,
    }
    fn = f"cert_{'lambda' if use_tl else 'base'}_{lam_str.replace('.', 'p')}.json"
    with open(__file__.rsplit("/", 1)[0] + "/" + fn, "w") as f:
        json.dump(tree_out, f)
    print(
        f"lambda={lam_str}: D*={bb.incumbent} ({float(bb.incumbent):.9f}) leaves={bb.leaves} "
        f"internal={bb.internal} depth={bb.max_depth} lp_calls={bb.lp_calls} time={time.time()-t0:.1f}s -> {fn}",
        flush=True,
    )
    print("   point:", tree_out["attained_point"], flush=True)


if __name__ == "__main__":
    use_tl = "--no-tl" not in sys.argv
    for arg in sys.argv[1:]:
        if not arg.startswith("-"):
            run(arg, use_tl)
