"""Piecewise-linear encoding, MILP cutting-plane solver, and exact rational
branch-and-bound + Farkas certificate generator for the (**)
collision inequality family on the BLT v2 exponent program at lambda = 1.
"""
from fractions import Fraction as F
from itertools import permutations, product
import json
import math
from pathlib import Path
import sys
import time

import numpy as np
from scipy.optimize import linprog

ZERO = F(0)
R6 = range(1, 7)
LETTERS = ("a", "b", "c")
COPRIME_PAIRS = tuple(
    (j, k) for j in R6 for k in R6 if j < k and math.gcd(j, k) == 1
)
SUBSETS = tuple(tuple(i for i in R6 if (m >> (i - 1)) & 1) for m in range(64))
NONEMPTY_SUBSETS = tuple(S for S in SUBSETS if S)

# B-side difference caps from Lemma 3.1 when O_C is empty and |I_B| = 2:
#   (2,3): fix exp-2 -> cubic (2*b2); fix exp-3 -> quadratic (2*b3)
#   (3,4): fix exp-3 -> quadratic in y^2 (2*b3); fix exp-4 -> cubic (2*b4)
#   (2,5),(3,5): fix exp-5 -> quadratic/cubic (2*b5)
#   (4,5): fix exp-5 -> quadratic in x^2 (2*b5)
DIFF_CAPS = {
    (2, 3): (2, 3),
    (3, 4): (3, 4),
    (2, 5): (5,),
    (3, 5): (5,),
    (4, 5): (5,),
}

VAR_NAMES = (
    [f"a{i}" for i in R6]
    + ["a"]
    + [f"b{i}" for i in R6]
    + ["b"]
    + [f"c{i}" for i in R6]
    + ["c"]
    + ["Fa", "Fb", "Fc", "D"]
)
IDX = {name: i for i, name in enumerate(VAR_NAMES)}
N_VARS = len(VAR_NAMES)
D_IDX = IDX["D"]


def make_row(terms, rhs=0):
    row = [ZERO] * N_VARS
    for k, v in terms.items():
        if v != 0:
            row[IDX[k]] += F(v)
    return (tuple(row), F(rhs))


def build_v2_base_rows(lam=F(1)):
    """Return the 22 pure BLT v2 base linear inequalities (no Thue/Det) + WLOG S3 ordering."""
    rows = []
    rows.append(make_row({"a": 1, "b": 1, "c": 1}, lam))
    for s in LETTERS:
        t = {f"{s}{i}": 1 for i in R6}
        t[s] = -1
        rows.append(make_row(t, 0))
        t2 = {f"{s}{i}": -(7 - i) for i in R6}
        t2[s] = 7
        rows.append(make_row(t2, 1))
    rows.append(make_row({"D": 1, "a": -1, "b": -1}, 0))
    rows.append(make_row({"D": 1, "a": -1, "c": -1}, 0))
    rows.append(make_row({"D": 1, "b": -1, "c": -1}, 0))
    for s in LETTERS:
        for j in (2, 3, 5):
            t = {f"{s}{i}": 1 for i in R6 if i % j == 0}
            t[f"F{s}"] = -1
            rows.append(make_row(t, 0))
    rows.append(
        make_row({"Fa": 1, "Fb": 1, "Fc": 1, "a": -4, "b": -4, "c": -4, "D": 6}, 0)
    )
    # WLOG S3 symmetry breaking on the S3-invariant problem: a4 + 2*a5 >= b4 + 2*b5 >= c4 + 2*c5
    rows.append(make_row({"b4": 1, "b5": 2, "a4": -1, "a5": -2}, 0))
    rows.append(make_row({"c4": 1, "c5": 2, "b4": -1, "b5": -2}, 0))
    return rows


def cond_to_rows(cond):
    """Convert a branch condition tuple into linear inequality rows (a, rhs) meaning a.x <= rhs.

    Supported condition kinds:
      - ("geo", I, J, K, br):
          br in {0, 1} for the two branches of (B4).
      - ("ss", A, pA, B, IB, kB, OC, br):
          General (**) collision constraint for:
            A != B in {'a','b','c'}, C = third letter
            pA = (jA, kA) with 1 <= jA < kA <= 6 and gcd(jA, kA) == 1
            IB = non-empty subset of {1..6}
            kB in IB
            OC = subset of {1..6} (possibly empty)
          3 positive parts:
            arg1 = 2*alpha_{A,jA} - w_B
            arg2 = 2*alpha_{A,kA} - w_B
            arg3 = alpha_{B,kB} - w_C
          br == 0: diagonal branch D <= f_A + f_B + alpha_C
          br in 1..8: off-diagonal branch on closed sign octant (sig1, sig2, sig3) in {0,1}^3
            where br - 1 = 4*sig1 + 2*sig2 + sig3.
    """
    kind = cond[0]
    if kind == "geo":
        _, I, J, K, br = cond
        if br == 0:
            t = {"D": 1, "a": -1, "b": -1, "c": -1}
            for i in I:
                t[f"a{i}"] = t.get(f"a{i}", 0) + 1
            for i in J:
                t[f"b{i}"] = t.get(f"b{i}", 0) + 1
            for i in K:
                t[f"c{i}"] = t.get(f"c{i}", 0) + 1
            return [make_row(t, 0)]
        elif br == 1:
            t = {"D": 1, "a": -1, "b": -1, "c": -1}
            for i in I:
                t[f"a{i}"] = t.get(f"a{i}", 0) - (i - 1)
            for i in J:
                t[f"b{i}"] = t.get(f"b{i}", 0) - (i - 1)
            for i in K:
                t[f"c{i}"] = t.get(f"c{i}", 0) - (i - 1)
            return [make_row(t, -1)]
        else:
            raise ValueError(f"Invalid geo branch {br}")

    if kind == "ss":
        _, A, pA, B, IB, kB, OC, br = cond
        C = next(s for s in LETTERS if s not in (A, B))
        jA, kA = pA
        IB = tuple(IB)
        OC = tuple(OC)
        if br == 0:
            # D - f_A - f_B - alpha_C <= 0
            t = {"D": F(1), A: -F(1), B: -F(1), C: -F(1)}
            t[f"{A}{jA}"] = t.get(f"{A}{jA}", ZERO) + F(1)
            t[f"{A}{kA}"] = t.get(f"{A}{kA}", ZERO) + F(1)
            for i in IB:
                t[f"{B}{i}"] = t.get(f"{B}{i}", ZERO) + F(1)
            return [make_row(t, 0)]
        elif 1 <= br <= 8:
            sig1 = ((br - 1) >> 2) & 1
            sig2 = ((br - 1) >> 1) & 1
            sig3 = (br - 1) & 1

            # w_B = 7*B - sum_{i in IB} 7*B_i - sum_{i not in IB} (7-i)*B_i
            wB = {B: F(7)}
            for i in R6:
                wB[f"{B}{i}"] = -F(7) if i in IB else -F(7 - i)

            # w_C = sum_{i in OC} i * C_i
            wC = {f"{C}{i}": F(i) for i in OC}

            out_rows = []
            # Sign row 1: (1 if sig1==0 else -1) * (2*A_jA - w_B) <= 0
            s1_sign = F(1) if sig1 == 0 else -F(1)
            t1 = {k: -s1_sign * v for k, v in wB.items()}
            t1[f"{A}{jA}"] = t1.get(f"{A}{jA}", ZERO) + F(2) * s1_sign
            out_rows.append(make_row(t1, 0))

            # Sign row 2: (1 if sig2==0 else -1) * (2*A_kA - w_B) <= 0
            s2_sign = F(1) if sig2 == 0 else -F(1)
            t2 = {k: -s2_sign * v for k, v in wB.items()}
            t2[f"{A}{kA}"] = t2.get(f"{A}{kA}", ZERO) + F(2) * s2_sign
            out_rows.append(make_row(t2, 0))

            # Sign row 3: (1 if sig3==0 else -1) * (B_kB - w_C) <= 0
            s3_sign = F(1) if sig3 == 0 else -F(1)
            t3 = {k: -s3_sign * v for k, v in wC.items()}
            t3[f"{B}{kB}"] = t3.get(f"{B}{kB}", ZERO) + s3_sign
            out_rows.append(make_row(t3, 0))

            # Common part of D - f_A - f_B - 1/2 alpha_C - 1/2 f_C - 1/2 kappa - 1/2 delta <= 0:
            # Base without -1/2 delta:
            base_t = {"D": F(1), A: -F(1), B: -F(1), C: -F(1, 2)}
            # From -f_A = -A + p + q, and -1/2 kappa = -1/2(p + q + sig1*(p - wB/2) + sig2*(q - wB/2)):
            base_t[f"{A}{jA}"] = base_t.get(f"{A}{jA}", ZERO) + F(1) - F(1 + sig1, 2)
            base_t[f"{A}{kA}"] = base_t.get(f"{A}{kA}", ZERO) + F(1) - F(1 + sig2, 2)
            if sig1 + sig2 > 0:
                scale_wB = F(sig1 + sig2, 4)
                for k, v in wB.items():
                    base_t[k] = base_t.get(k, ZERO) + scale_wB * v
            # From -f_B: +B_i for i in IB
            for i in IB:
                base_t[f"{B}{i}"] = base_t.get(f"{B}{i}", ZERO) + F(1)
            # From -1/2 f_C: -1/2 C_i for i in OC
            for i in OC:
                base_t[f"{C}{i}"] = base_t.get(f"{C}{i}", ZERO) - F(1, 2)

            # Cap 1: delta_lock = sum_{i in IB \ {kB}} B_i + sig3 * (B_kB - w_C)
            t_lock = dict(base_t)
            for i in IB:
                if i != kB:
                    t_lock[f"{B}{i}"] = t_lock.get(f"{B}{i}", ZERO) - F(1, 2)
            if sig3 == 1:
                t_lock[f"{B}{kB}"] = t_lock.get(f"{B}{kB}", ZERO) - F(1, 2)
                for k, v in wC.items():
                    t_lock[k] = t_lock.get(k, ZERO) + F(1, 2) * v
            out_rows.append(make_row(t_lock, 0))

            # Additional difference caps when OC is empty and IB in DIFF_CAPS: delta_cap = 2 * B_idx
            if not OC and IB in DIFF_CAPS:
                for idx in DIFF_CAPS[IB]:
                    t_cap = dict(base_t)
                    t_cap[f"{B}{idx}"] = t_cap.get(f"{B}{idx}", ZERO) - F(1)
                    out_rows.append(make_row(t_cap, 0))

            return out_rows
        else:
            raise ValueError(f"Invalid ss branch {br}")

    raise ValueError(f"Unknown condition kind: {kind}")


# Precompute all O_C = () instances (with canonical kB = IB[0]) for fast vectorized separation
SS0_KEYS = tuple(
    (A, pA, B, IB, IB[0], ())
    for A, B in permutations(LETTERS, 2)
    for pA in COPRIME_PAIRS
    for IB in NONEMPTY_SUBSETS
)


def top_violated_geo_float(xf, k, tol=1e-9):
    """Find top k genuinely distinct violated (B4) constraints at float vector xf.
    Always includes 1 in I_s (which strictly dominates omitting 1), and only includes
    i >= 2 in I_s if xf[s_i] > 1e-7 so zero coordinates do not create tied duplicates.
    """
    L = xf[IDX["a"]] + xf[IDX["b"]] + xf[IDX["c"]]
    D = xf[D_IDX]
    opts = {}
    for s in LETTERS:
        active_i = [i for i in range(2, 7) if xf[IDX[f"{s}{i}"]] > 1e-7]
        s_opts = []
        for mask in range(1 << len(active_i)):
            I = (1,) + tuple(active_i[b] for b in range(len(active_i)) if (mask >> b) & 1)
            s0 = sum(xf[IDX[f"{s}{i}"]] for i in I)
            s1 = sum((i - 1) * xf[IDX[f"{s}{i}"]] for i in I)
            s_opts.append((I, s0, s1))
        opts[s] = s_opts
    cands = []
    for Ia, s0a, s1a in opts["a"]:
        for Ib, s0b, s1b in opts["b"]:
            for Ic, s0c, s1c in opts["c"]:
                v = max(L - (s0a + s0b + s0c), L - 1.0 + (s1a + s1b + s1c))
                if D - v > tol:
                    cands.append((D - v, ("geo", Ia, Ib, Ic)))
    cands.sort(key=lambda t: -t[0])
    return [c for _, c in cands[:k]]


def top_violated_ss0_float(xf, k, tol=1e-9):
    """Find top k genuinely distinct violated O_C = empty (**) constraints at xf.
    Avoids tied duplicates from zero coordinates by requiring active coordinates in pA and IB.
    """
    D = xf[D_IDX]
    out = []
    for A, B in permutations(LETTERS, 2):
        C = next(s for s in LETTERS if s not in (A, B))
        xA = xf[IDX[A]]
        xB = xf[IDX[B]]
        xC = xf[IDX[C]]
        coordsA = [xf[IDX[f"{A}{i}"]] for i in R6]
        coordsB = [xf[IDX[f"{B}{i}"]] for i in R6]
        tailB = 7.0 * (xB - sum(coordsB))
        active_B = [i for i in R6 if coordsB[i - 1] > 1e-7]
        # Candidate sets IB: all non-empty subsets of active_B, plus DIFF_CAPS pairs with at least one active coord
        ib_set = set()
        for mask in range(1, 1 << len(active_B)):
            ib_set.add(tuple(active_B[b] for b in range(len(active_B)) if (mask >> b) & 1))
        for dc in DIFF_CAPS:
            if coordsB[dc[0] - 1] + coordsB[dc[1] - 1] > 1e-7:
                ib_set.add(dc)
        active_pAs = [pA for pA in COPRIME_PAIRS if coordsA[pA[0] - 1] + coordsA[pA[1] - 1] > 1e-7]
        if not active_pAs:
            active_pAs = [(2, 3)]
        for IB in sorted(ib_set):
            sumIB = sum(coordsB[i - 1] for i in IB)
            fB = xB - sumIB
            wB = sum(i * coordsB[i - 1] for i in R6 if i not in IB) + tailB
            delta = sumIB
            if IB in DIFF_CAPS:
                for idx in DIFF_CAPS[IB]:
                    if 2.0 * coordsB[idx - 1] < delta:
                        delta = 2.0 * coordsB[idx - 1]
            for pA in active_pAs:
                p = coordsA[pA[0] - 1]
                q = coordsA[pA[1] - 1]
                fA = xA - p - q
                kappa = p + q + 0.5 * (
                    max(0.0, 2.0 * p - wB) + max(0.0, 2.0 * q - wB)
                )
                diag = fA + fB + xC
                off = fA + fB + 0.5 * (xC + delta + kappa)
                v = diag if diag >= off else off
                if D - v > tol:
                    out.append((D - v, ("ss", A, pA, B, IB, IB[0], ())))
    out.sort(key=lambda t: -t[0])
    return [c for _, c in out[:k]]


# ----------------------------------------------------------------- exact rational dual extraction
def solve_rational(A, b):
    """Solve A x = b over Fraction. Free variables -> 0. None if inconsistent."""
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
    for j in range(N_VARS):
        s = sum(v * rows[i][0][j] for i, v in y.items())
        if j == D_IDX:
            if s != 1:
                return None
        elif s < 0:
            return None
    return sum(v * rows[i][1] for i, v in y.items())


def is_redundant_neg_unit_row(r_vec, r_rhs):
    """True if the row is -x_j <= 0 for a single variable x_j (always redundant since x_j >= 0)."""
    if r_rhs != 0:
        return False
    nz = [(j, v) for j, v in enumerate(r_vec) if v != 0]
    return len(nz) == 1 and nz[0][1] < 0


def repair_float_dual(rows, yf, K):
    """Round float dual yf >= 0 with denominator K and repair any negative column sums
    using base rows 19, 1, 3, 5, 0, then normalize so (y^T A)_D == 1.
    """
    y = {}
    for i, v in enumerate(yf):
        if v > 1e-12 and not is_redundant_neg_unit_row(rows[i][0], rows[i][1]):
            num = math.ceil(float(v) * K)
            if num > 0:
                y[i] = F(num, K)
    if not y:
        return None, None

    def col_sums(yd):
        c = [ZERO] * N_VARS
        for i, v in yd.items():
            r = rows[i][0]
            for j in range(N_VARS):
                if r[j]:
                    c[j] += v * r[j]
        return c

    c = col_sums(y)
    # Step 1: repair Fa, Fb, Fc (indices 21, 22, 23) using Row 19 (Fa+Fb+Fc - 4(a+b+c) + 6D <= 0)
    dF = max(ZERO, -c[21], -c[22], -c[23])
    if dF > 0:
        y[19] = y.get(19, ZERO) + dF
        c = col_sums(y)
    # Step 2: repair s1..s6 using Rows 1, 3, 5 (sum_{i=1}^6 s_i - s <= 0)
    changed = False
    for s_idx, r_idx in enumerate((1, 3, 5)):
        base = s_idx * 7
        ds = max([ZERO] + [-c[base + k] for k in range(6)])
        if ds > 0:
            y[r_idx] = y.get(r_idx, ZERO) + ds
            changed = True
    if changed:
        c = col_sums(y)
    # Step 3: repair a, b, c (indices 6, 13, 20) using Row 0 (a + b + c <= lam)
    dt = max(ZERO, -c[6], -c[13], -c[20])
    if dt > 0:
        y[0] = y.get(0, ZERO) + dt
        c = col_sums(y)
    cD = c[D_IDX]
    if cD <= 0:
        return None, None
    y_norm = {i: v / cD for i, v in y.items() if v > 0}
    bd = verify_farkas(rows, y_norm)
    return (y_norm, bd) if bd is not None else (None, None)


def certify_leaf_below(rows, xf, yf, target_D):
    """Given a leaf LP solution with float value < target_D, return (y, bound) with exact bound < target_D."""
    m = len(rows)
    # Try exact rational basis solve first if it produces a clean small denominator
    T = [v for v in range(N_VARS) if xf[v] > 1e-9 or v == D_IDX]
    S = [
        i
        for i in range(m)
        if yf[i] > 1e-9 and not is_redundant_neg_unit_row(rows[i][0], rows[i][1])
    ]
    if S:
        sol = solve_rational(
            [[rows[i][0][v] for i in S] for v in T],
            [F(1) if v == D_IDX else ZERO for v in T],
        )
        if sol is not None:
            y = {i: v for i, v in zip(S, sol) if v != 0}
            bd = verify_farkas(rows, y)
            if bd is not None and bd < target_D and bd.denominator <= 1000000:
                return y, bd
    # Fast exact K-repair fallback
    for K in (1000, 10000, 100000, 1000000, 10000000):
        y, bd = repair_float_dual(rows, yf, K)
        if y is not None and bd < target_D:
            return y, bd
    return None, None


def certify_infeasible_leaf(rows, target_D):
    """When rows x <= b, x >= 0 is infeasible, return (y, bound) with bound < target_D."""
    m = len(rows)
    A = np.array([[float(c) for c in r] + [-1.0] for r, _ in rows])
    b = np.array([float(bb) for _, bb in rows])
    c = np.zeros(N_VARS + 1)
    c[N_VARS] = 1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * (N_VARS + 1), method="highs")
    assert res.status == 0 and res.fun > 1e-9, f"Expected infeasible LP, got {res.status} {res.fun}"
    yf = -res.ineqlin.marginals
    for K in (1000, 10000, 100000, 1000000):
        y = {}
        for i, v in enumerate(yf):
            if v > 1e-12 and not is_redundant_neg_unit_row(rows[i][0], rows[i][1]):
                num = math.ceil(float(v) * K)
                if num > 0:
                    y[i] = F(num, K)
        if not y:
            continue

        def col_sums(yd):
            cs = [ZERO] * N_VARS
            for i, v in yd.items():
                r = rows[i][0]
                for j in range(N_VARS):
                    if r[j]:
                        cs[j] += v * r[j]
            return cs

        cs = col_sums(y)
        dF = max(ZERO, -cs[21], -cs[22], -cs[23])
        if dF > 0:
            y[19] = y.get(19, ZERO) + dF
            cs = col_sums(y)
        for s_idx, r_idx in enumerate((1, 3, 5)):
            base = s_idx * 7
            ds = max([ZERO] + [-cs[base + k] for k in range(6)])
            if ds > 0:
                y[r_idx] = y.get(r_idx, ZERO) + ds
        cs = col_sums(y)
        dt = max(ZERO, -cs[6], -cs[13], -cs[20])
        if dt > 0:
            y[0] = y.get(0, ZERO) + dt
            cs = col_sums(y)
        # Ensure (y^T A)_D >= 0; if < 0, add (-cs[D_IDX]) of Row 7 (D - a - b <= 0) + Row 0 (a + b + c <= 1)
        if cs[D_IDX] < 0:
            need = -cs[D_IDX]
            y[7] = y.get(7, ZERO) + need
            y[0] = y.get(0, ZERO) + need
            cs = col_sums(y)
        yb = sum(v * rows[i][1] for i, v in y.items())
        if yb < 0:
            # Combine with y0 = {0: 1, 7: 1} which has (y0^T A)_D = 1 and y0^T b = rows[0][1] = 1:
            # Set t = -1 / yb > 0 so that (1 + t * yb) == 0 -> bound == 0 < target_D!
            t = -rows[0][1] / yb
            scale = F(1) + t * cs[D_IDX]
            y_comb = {0: F(1) / scale, 7: F(1) / scale}
            for i, v in y.items():
                y_comb[i] = y_comb.get(i, ZERO) + (t * v) / scale
            y_comb = {i: v for i, v in y_comb.items() if v > 0}
            bd = verify_farkas(rows, y_comb)
            if bd is not None and bd < target_D:
                return y_comb, bd
    raise RuntimeError("Could not certify infeasible leaf")


def solve_lp(rows):
    A = np.array([[float(c) for c in r] for r, _ in rows])
    b = np.array([float(bb) for _, bb in rows])
    c = np.zeros(N_VARS)
    c[D_IDX] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * N_VARS, method="highs")
    if res.status == 2:
        return "infeasible", None, None
    if res.status != 0:
        raise RuntimeError(res.message)
    return "optimal", res.x, -res.ineqlin.marginals


# ----------------------------------------------------------------- branch and bound generator
class BBStarStar:
    def __init__(self, target_D, lam=F(1), k_geo=5, k_ss=6):
        self.target_D = F(target_D)
        self.target_float = float(self.target_D)
        self.lam = F(lam)
        self.base = build_v2_base_rows(self.lam)
        self.k_geo = k_geo
        self.k_ss = k_ss
        self.leaves = 0
        self.geo_nodes = 0
        self.ss_nodes = 0
        self.lp_calls = 0
        self.max_depth = 0
        self.max_certified_D = ZERO
        self.t0 = time.time()

    def rows_for(self, conds):
        rows = list(self.base)
        for c in conds:
            rows.extend(cond_to_rows(c))
        return rows

    def make_leaf(self, y, bound):
        self.leaves += 1
        if bound > self.max_certified_D:
            self.max_certified_D = bound
        return {
            "type": "leaf",
            "y": {str(i): str(v) for i, v in sorted(y.items())},
            "bound": str(bound),
        }

    def clone_subtree(self, node):
        import copy

        if node["type"] == "leaf":
            self.leaves += 1
            return copy.deepcopy(node)
        elif node["type"] == "geo":
            self.geo_nodes += 1
            return {
                "type": "geo",
                "I": list(node["I"]),
                "J": list(node["J"]),
                "K": list(node["K"]),
                "children": [self.clone_subtree(ch) for ch in node["children"]],
            }
        else:
            self.ss_nodes += 1
            return {
                "type": "ss",
                "A": node["A"],
                "pA": list(node["pA"]),
                "B": node["B"],
                "IB": list(node["IB"]),
                "kB": node["kB"],
                "OC": list(node["OC"]),
                "children": [self.clone_subtree(ch) for ch in node["children"]],
            }

    def solve_node(self, conds, depth=0):
        if depth > self.max_depth:
            self.max_depth = depth
        rows = self.rows_for(conds)
        self.lp_calls += 1
        if self.lp_calls % 500 == 0:
            print(
                f"  [bb] lp_calls={self.lp_calls} leaves={self.leaves} geo={self.geo_nodes} ss={self.ss_nodes} "
                f"depth={depth} max_D={float(self.max_certified_D):.7f} t={time.time()-self.t0:.1f}s",
                flush=True,
            )
        status, xf, yf = solve_lp(rows)
        if status == "infeasible":
            y, bd = certify_infeasible_leaf(rows, self.target_D)
            return self.make_leaf(y, bd)
        if xf[D_IDX] < self.target_float - 1e-9:
            y, bd = certify_leaf_below(rows, xf, yf, self.target_D)
            if y is not None and bd < self.target_D:
                return self.make_leaf(y, bd)

        # Node is open: collect violated (B4) and (**) (O_C=empty) candidates
        used_keys = {c[:-1] for c in conds}
        geo_cands = [
            c for c in top_violated_geo_float(xf, self.k_geo + 4, tol=1e-7) if c not in used_keys
        ][: self.k_geo]
        ss_cands = [
            c for c in top_violated_ss0_float(xf, self.k_ss + 6, tol=1e-7) if c not in used_keys
        ][: self.k_ss]
        if not geo_cands and not ss_cands:
            geo_cands = [
                c for c in top_violated_geo_float(xf, 20, tol=-1.0) if c not in used_keys
            ][:4]
            ss_cands = [
                c for c in top_violated_ss0_float(xf, 20, tol=-1.0) if c not in used_keys
            ][:4]

        best = None
        for cand in geo_cands + ss_cands:
            if cand[0] == "geo":
                eval_brs = (0, 1)
                n_total_brs = 2
            else:
                # For O_C = (), branches with sig3=0 (br in 1,3,5,7) are subsets of sig3=1 (br in 2,4,6,8),
                # so we only need to evaluate the 5 active branches (0, 2, 4, 6, 8)
                eval_brs = (0, 2, 4, 6, 8) if not cand[6] else range(9)
                n_total_brs = 5 if not cand[6] else 9
            vals = []
            for br in eval_brs:
                cc = conds + (cand + (br,),)
                st, xx, _ = solve_lp(self.rows_for(cc))
                self.lp_calls += 1
                vals.append(xx[D_IDX] if st == "optimal" else -1.0)
            n_open = sum(1 for v in vals if v >= self.target_float - 1e-8)
            max_v = max(vals)
            open_excess = sum(max(0.0, v - self.target_float) for v in vals)
            if n_open == 0:
                score = (0, n_total_brs, round(max_v, 7))
            else:
                score = (1, round(max_v, 6), n_open, round(open_excess, 6), n_total_brs)
            if best is None or score < best[0]:
                best = (score, cand)

        _, chosen = best
        if chosen[0] == "geo":
            self.geo_nodes += 1
            _, I, J, K = chosen
            children = [self.solve_node(conds + (chosen + (br,),), depth + 1) for br in (0, 1)]
            return {"type": "geo", "I": list(I), "J": list(J), "K": list(K), "children": children}
        else:
            self.ss_nodes += 1
            _, A, pA, B, IB, kB, OC = chosen
            if not OC:
                children = [None] * 9
                children[0] = self.solve_node(conds + (chosen + (0,),), depth + 1)
                for m in range(4):
                    br_neg = 1 + 2 * m
                    br_pos = 2 + 2 * m
                    children[br_pos] = self.solve_node(conds + (chosen + (br_pos,),), depth + 1)
                    if children[br_pos]["type"] == "leaf":
                        children[br_neg] = self.clone_subtree(children[br_pos])
                    else:
                        # Try closing br_neg as a single leaf first (since B_kB <= 0 is active on br_neg)
                        rows_neg = self.rows_for(conds + (chosen + (br_neg,),))
                        self.lp_calls += 1
                        st_n, xf_n, yf_n = solve_lp(rows_neg)
                        closed_single = False
                        if st_n == "infeasible":
                            y_n, bd_n = certify_infeasible_leaf(rows_neg, self.target_D)
                            children[br_neg] = self.make_leaf(y_n, bd_n)
                            closed_single = True
                        elif xf_n[D_IDX] < self.target_float - 1e-9:
                            y_n, bd_n = certify_leaf_below(rows_neg, xf_n, yf_n, self.target_D)
                            if y_n is not None and bd_n < self.target_D:
                                children[br_neg] = self.make_leaf(y_n, bd_n)
                                closed_single = True
                        if not closed_single:
                            # Reuse the valid subtree from br_pos with zero extra LP calls!
                            children[br_neg] = self.clone_subtree(children[br_pos])
            else:
                children = [self.solve_node(conds + (chosen + (br,),), depth + 1) for br in range(9)]
            return {
                "type": "ss",
                "A": A,
                "pA": list(pA),
                "B": B,
                "IB": list(IB),
                "kB": kB,
                "OC": list(OC),
                "children": children,
            }


# ----------------------------------------------------------------- PuLP MILP encoding
def add_one_starstar_pulp(P, V, D, A, pA, B, IB, kB, OC=(), use_cap=True, tag_id=0):
    """Add one (**) piecewise-linear constraint to a PuLP model (P, V, D)."""
    import pulp

    C = next(s for s in LETTERS if s not in (A, B))
    IB = tuple(IB)
    OC = tuple(OC)
    tag = f"{tag_id}_{A}{pA[0]}{pA[1]}_{B}{''.join(map(str, IB))}_k{kB}_C{''.join(map(str, OC))}"
    p, q = V[A, pA[0]], V[A, pA[1]]
    fA = V[A] - p - q
    fB = V[B] - pulp.lpSum(V[B, i] for i in IB)
    wB = pulp.lpSum(i * V[B, i] for i in R6 if i not in IB) + 7 * (
        V[B] - pulp.lpSum(V[B, i] for i in R6)
    )
    fC = pulp.lpSum(V[C, i] for i in OC)
    wC = pulp.lpSum(i * V[C, i] for i in OC)

    def pos_part(expr, suffix):
        h = pulp.LpVariable(f"ss_pos_{tag}_{suffix}", 0)
        z = pulp.LpVariable(f"ss_sign_{tag}_{suffix}", cat="Binary")
        P += h >= expr
        P += h <= expr + 1.0 * (1 - z)
        P += h <= 1.0 * z
        return h

    h1 = pos_part(2 * p - wB, "p")
    h2 = pos_part(2 * q - wB, "q")
    h3 = pos_part(V[B, kB] - wC, "kB")
    kappa = p + q + 0.5 * (h1 + h2)
    delta_lock = pulp.lpSum(V[B, i] for i in IB if i != kB) + h3
    zc = pulp.LpVariable(f"ss_cauchy_{tag}", cat="Binary")
    P += D <= fA + fB + V[C] + 1.0 * zc
    deltas = [delta_lock]
    if use_cap and not OC and IB in DIFF_CAPS:
        deltas.extend(2 * V[B, idx] for idx in DIFF_CAPS[IB])
    for dl in deltas:
        P += D <= fA + fB + fC + 0.5 * ((V[C] - fC) + dl + kappa) + 1.0 * (1 - zc)
    return P


if __name__ == "__main__":
    target_str = sys.argv[1] if len(sys.argv) > 1 else "54/91"
    target_D = F(target_str)
    print(f"Running BBStarStar with D_target = {target_D} ({float(target_D):.9f}) ...", flush=True)
    bb = BBStarStar(target_D)
    sys.setrecursionlimit(10000)
    tree = bb.solve_node((), 0)
    elapsed = time.time() - bb.t0
    out = {
        "lambda": "1",
        "D_target": str(target_D),
        "max_certified_D": str(bb.max_certified_D),
        "lower_bound_witness_D": "213/359",
        "leaves": bb.leaves,
        "geo_nodes": bb.geo_nodes,
        "ss_nodes": bb.ss_nodes,
        "max_depth": bb.max_depth,
        "lp_calls": bb.lp_calls,
        "elapsed_seconds": round(elapsed, 2),
        "tree": tree,
    }
    out_path = Path(__file__).with_name("cert_starstar.json")
    with open(out_path, "w") as f:
        json.dump(out, f)
    print(
        f"DONE: D_target={target_D} ({float(target_D):.9f}), max_certified_D={bb.max_certified_D} "
        f"({float(bb.max_certified_D):.9f}), leaves={bb.leaves}, geo={bb.geo_nodes}, ss={bb.ss_nodes}, "
        f"depth={bb.max_depth}, lp_calls={bb.lp_calls}, time={elapsed:.2f}s -> {out_path}"
    )
