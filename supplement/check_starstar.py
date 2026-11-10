"""Independent exact rational verifier for the (**) branch-and-bound
Farkas certificate (cert_starstar.json) and the exact feasible witness points.

Uses ONLY the Python standard library (fractions.Fraction, json, math, itertools, copy).
Does NOT import lp_starstar.py or any other project script.

Run:
    python3 check_starstar.py
"""
from collections import Counter
import copy
from fractions import Fraction as F
from itertools import permutations, product
import json
import math
from pathlib import Path
import sys
import time

ZERO = F(0)
ONE = F(1)
HALF = F(1, 2)
R6 = range(1, 7)
LETTERS = ("a", "b", "c")
COPRIME_PAIRS = tuple(
    (j, k) for j in R6 for k in R6 if j < k and math.gcd(j, k) == 1
)
SUBSETS = tuple(tuple(i for i in R6 if (m >> (i - 1)) & 1) for m in range(64))
NONEMPTY_SUBSETS = tuple(S for S in SUBSETS if S)

# B-side difference caps from Lemma 3.1 when O_C = empty and |I_B| = 2
DIFF_CAPS = {
    (2, 3): (2, 3),
    (3, 4): (3, 4),
    (2, 5): (5,),
    (3, 5): (5,),
    (4, 5): (5,),
}

VAR_NAMES = tuple(
    [f"a{i}" for i in R6]
    + ["a"]
    + [f"b{i}" for i in R6]
    + ["b"]
    + [f"c{i}" for i in R6]
    + ["c"]
    + ["Fa", "Fb", "Fc", "D"]
)
POS = {name: i for i, name in enumerate(VAR_NAMES)}
N_VARS = len(VAR_NAMES)
D_IDX = POS["D"]


class VerificationError(Exception):
    """Raised when any certificate check fails."""


def require(cond, msg):
    if not cond:
        raise VerificationError(msg)


def make_row(terms, rhs=0):
    vec = [ZERO] * N_VARS
    for name, coeff in terms.items():
        require(name in POS, f"Unknown variable {name}")
        vec[POS[name]] += F(coeff)
    return (tuple(vec), F(rhs))


def dot(row_vec, x_vec):
    return sum((a * b for a, b in zip(row_vec, x_vec) if a and b), ZERO)


def build_base_rows(lam=ONE):
    """Reconstruct the 22 base linear inequalities (B1)-(B3) + WLOG S3 ordering (5.1)."""
    rows = []
    # (B1) L = a + b + c <= lam
    rows.append(make_row({"a": 1, "b": 1, "c": 1}, lam))
    # (B1) coordinate sum <= s and height budget 7*s - sum_{i=1}^6 (7-i)*s_i <= 1
    for s in LETTERS:
        t_sum = {f"{s}{i}": 1 for i in R6}
        t_sum[s] = -1
        rows.append(make_row(t_sum, 0))
        t_ht = {f"{s}{i}": -(7 - i) for i in R6}
        t_ht[s] = 7
        rows.append(make_row(t_ht, 1))
    # (B2) Trivial bounds D <= a+b, a+c, b+c
    for s, t in (("a", "b"), ("a", "c"), ("b", "c")):
        rows.append(make_row({"D": 1, s: -1, t: -1}, 0))
    # (B3) Fourier bounds sum_{j|i} s_i <= F_s for j in (2,3,5), and Fa+Fb+Fc <= 4*L - 6*D
    for s in LETTERS:
        for j in (2, 3, 5):
            t_f = {f"{s}{i}": 1 for i in R6 if i % j == 0}
            t_f[f"F{s}"] = -1
            rows.append(make_row(t_f, 0))
    rows.append(
        make_row({"Fa": 1, "Fb": 1, "Fc": 1, "a": -4, "b": -4, "c": -4, "D": 6}, 0)
    )
    # (5.1) WLOG S3 symmetry-breaking ordering: a4 + 2*a5 >= b4 + 2*b5 >= c4 + 2*c5
    rows.append(make_row({"b4": 1, "b5": 2, "a4": -1, "a5": -2}, 0))
    rows.append(make_row({"c4": 1, "c5": 2, "b4": -1, "b5": -2}, 0))
    require(len(rows) == 22, f"Expected 22 base rows, got {len(rows)}")
    return rows


def check_strictly_increasing_subset(lst, allow_empty=True, label="subset"):
    require(isinstance(lst, (list, tuple)), f"{label} must be list/tuple")
    if not allow_empty:
        require(len(lst) > 0, f"{label} must be non-empty")
    for idx, val in enumerate(lst):
        require(type(val) is int and 1 <= val <= 6, f"Invalid element {val} in {label}")
        if idx > 0:
            require(lst[idx - 1] < val, f"{label} not strictly increasing: {lst}")
    return tuple(lst)


def geo_branches(I, J, K):
    """Return the 2 branch row-lists for (B4) with subsets (I, J, K)."""
    I = check_strictly_increasing_subset(I, allow_empty=True, label="I")
    J = check_strictly_increasing_subset(J, allow_empty=True, label="J")
    K = check_strictly_increasing_subset(K, allow_empty=True, label="K")
    # Branch 0: D <= L - Sigma_0  <=>  D - L + Sigma_0 <= 0
    t0 = {"D": 1, "a": -1, "b": -1, "c": -1}
    for i in I:
        t0[f"a{i}"] = t0.get(f"a{i}", 0) + 1
    for i in J:
        t0[f"b{i}"] = t0.get(f"b{i}", 0) + 1
    for i in K:
        t0[f"c{i}"] = t0.get(f"c{i}", 0) + 1
    # Branch 1: D <= L - 1 + Sigma_1  <=>  D - L - Sigma_1 <= -1
    t1 = {"D": 1, "a": -1, "b": -1, "c": -1}
    for i in I:
        t1[f"a{i}"] = t1.get(f"a{i}", 0) - (i - 1)
    for i in J:
        t1[f"b{i}"] = t1.get(f"b{i}", 0) - (i - 1)
    for i in K:
        t1[f"c{i}"] = t1.get(f"c{i}", 0) - (i - 1)
    return [[make_row(t0, 0)], [make_row(t1, -1)]]


def ss_branches(A, pA, B, IB, kB, OC):
    """Return the 9 branch row-lists for (**) with parameters (A, pA, B, IB, kB, OC)."""
    require(A in LETTERS and B in LETTERS and A != B, f"Invalid letters A={A}, B={B}")
    C = next(s for s in LETTERS if s not in (A, B))
    pA = check_strictly_increasing_subset(pA, allow_empty=False, label="pA")
    require(len(pA) == 2 and math.gcd(pA[0], pA[1]) == 1, f"pA={pA} must be a coprime pair")
    IB = check_strictly_increasing_subset(IB, allow_empty=False, label="IB")
    require(type(kB) is int and kB in IB, f"kB={kB} must be an element of IB={IB}")
    OC = check_strictly_increasing_subset(OC, allow_empty=True, label="OC")

    jA, kA = pA
    # Branch 0: diagonal D <= f_A + f_B + C  <=>  D - f_A - f_B - C <= 0
    diag_t = {"D": ONE, A: -ONE, B: -ONE, C: -ONE}
    diag_t[f"{A}{jA}"] = diag_t.get(f"{A}{jA}", ZERO) + ONE
    diag_t[f"{A}{kA}"] = diag_t.get(f"{A}{kA}", ZERO) + ONE
    for i in IB:
        diag_t[f"{B}{i}"] = diag_t.get(f"{B}{i}", ZERO) + ONE
    branches = [[make_row(diag_t, 0)]]

    # w_B = 7*B - sum_{i in IB} 7*B_i - sum_{i not in IB} (7-i)*B_i
    wB = {B: F(7)}
    for i in R6:
        wB[f"{B}{i}"] = -F(7) if i in IB else -F(7 - i)
    wC = {f"{C}{i}": F(i) for i in OC}

    # Branches 1..8: 8 closed sign octants (sig1, sig2, sig3) in {0,1}^3
    for sig1, sig2, sig3 in product((0, 1), repeat=3):
        b_rows = []
        # Sign 1: (2*A_jA - w_B) <= 0 if sig1==0 else -(2*A_jA - w_B) <= 0
        s1 = ONE if sig1 == 0 else -ONE
        t1 = {k: -s1 * v for k, v in wB.items()}
        t1[f"{A}{jA}"] = t1.get(f"{A}{jA}", ZERO) + F(2) * s1
        b_rows.append(make_row(t1, 0))

        # Sign 2: (2*A_kA - w_B) <= 0 if sig2==0 else -(2*A_kA - w_B) <= 0
        s2 = ONE if sig2 == 0 else -ONE
        t2 = {k: -s2 * v for k, v in wB.items()}
        t2[f"{A}{kA}"] = t2.get(f"{A}{kA}", ZERO) + F(2) * s2
        b_rows.append(make_row(t2, 0))

        # Sign 3: (B_kB - w_C) <= 0 if sig3==0 else -(B_kB - w_C) <= 0
        s3 = ONE if sig3 == 0 else -ONE
        t3 = {k: -s3 * v for k, v in wC.items()}
        t3[f"{B}{kB}"] = t3.get(f"{B}{kB}", ZERO) + s3
        b_rows.append(make_row(t3, 0))

        # Off-diagonal inequalities: D - f_A - f_B - 1/2 C - 1/2 f_C - 1/2 kappa - 1/2 delta_tilde <= 0
        base_t = {"D": ONE, A: -ONE, B: -ONE, C: -HALF}
        base_t[f"{A}{jA}"] = base_t.get(f"{A}{jA}", ZERO) + ONE - F(1 + sig1, 2)
        base_t[f"{A}{kA}"] = base_t.get(f"{A}{kA}", ZERO) + ONE - F(1 + sig2, 2)
        if sig1 + sig2 > 0:
            scale_wB = F(sig1 + sig2, 4)
            for k, v in wB.items():
                base_t[k] = base_t.get(k, ZERO) + scale_wB * v
        for i in IB:
            base_t[f"{B}{i}"] = base_t.get(f"{B}{i}", ZERO) + ONE
        for i in OC:
            base_t[f"{C}{i}"] = base_t.get(f"{C}{i}", ZERO) - HALF

        # Cap 1: delta_lock = sum_{i in IB \ {kB}} B_i + sig3*(B_kB - w_C)
        t_lock = dict(base_t)
        for i in IB:
            if i != kB:
                t_lock[f"{B}{i}"] = t_lock.get(f"{B}{i}", ZERO) - HALF
        if sig3 == 1:
            t_lock[f"{B}{kB}"] = t_lock.get(f"{B}{kB}", ZERO) - HALF
            for k, v in wC.items():
                t_lock[k] = t_lock.get(k, ZERO) + HALF * v
        b_rows.append(make_row(t_lock, 0))

        # Lemma 3.1 difference caps when OC is empty and IB in DIFF_CAPS
        if not OC and IB in DIFF_CAPS:
            for idx in DIFF_CAPS[IB]:
                t_cap = dict(base_t)
                t_cap[f"{B}{idx}"] = t_cap.get(f"{B}{idx}", ZERO) - ONE
                b_rows.append(make_row(t_cap, 0))

        branches.append(b_rows)

    require(len(branches) == 9, f"Expected 9 branches, got {len(branches)}")
    return branches


def load_certificate(path):
    def no_dup_keys(pairs):
        obj = {}
        for k, v in pairs:
            require(k not in obj, f"Duplicate JSON key {k}")
            obj[k] = v
        return obj

    with open(path, "r", encoding="utf-8") as f:
        return json.load(f, object_pairs_hook=no_dup_keys)


def verify_certificate(cert_data, override_target_D=None, override_base_rows=None):
    """Verify the entire branch-and-bound Farkas tree in exact Fraction arithmetic.

    Checks at every leaf:
      1. y is a non-empty dict of strictly positive rational multipliers on valid row indices.
      2. Normalized dual form: (y^T A)_D == 1, (y^T A)_v >= 0 for all v != D,
         and bound := y^T b == Fraction(node['bound']) < target_D.
      3. Homogeneous Farkas infeasibility form for {A x <= b, -D <= -target_D, x >= 0}:
         with multiplier 1 on (-D <= -target_D), all 25 variable coefficients of
         (y^T A - e_D^T) are >= 0 and the combined RHS (y^T b - target_D) < 0.
    """
    require(isinstance(cert_data, dict) and "tree" in cert_data, "Missing tree in certificate")
    lam = F(cert_data.get("lambda", "1"))
    require(lam == ONE, f"Expected lambda=1, got {lam}")
    target_D = F(override_target_D) if override_target_D is not None else F(cert_data["D_target"])
    base = list(override_base_rows) if override_base_rows is not None else build_base_rows(lam)

    counts = Counter()
    max_depth = 0
    leaf_bounds = []

    def visit(node, rows, path):
        nonlocal max_depth
        require(isinstance(node, dict) and "type" in node, f"Invalid node at {path}")
        ntype = node["type"]
        counts[ntype] += 1
        if len(path) > max_depth:
            max_depth = len(path)

        if ntype == "leaf":
            require(
                set(node.keys()) == {"type", "y", "bound"},
                f"Unexpected leaf keys {set(node.keys())} at {path}",
            )
            y_dict = node["y"]
            require(isinstance(y_dict, dict) and len(y_dict) > 0, f"Empty dual y at {path}")
            col_sums = [ZERO] * N_VARS
            rhs_sum = ZERO
            for k_str, v_str in y_dict.items():
                require(isinstance(k_str, str) and k_str.isdigit(), f"Invalid row index key {k_str} at {path}")
                idx = int(k_str)
                require(str(idx) == k_str and 0 <= idx < len(rows), f"Row index {idx} out of range [0, {len(rows)}) at {path}")
                yv = F(v_str)
                require(yv > ZERO, f"Dual multiplier must be > 0, got {yv} at {path}")
                r_vec, r_rhs = rows[idx]
                for j in range(N_VARS):
                    if r_vec[j]:
                        col_sums[j] += yv * r_vec[j]
                rhs_sum += yv * r_rhs

            # Check 1: Normalized dual conditions
            require(
                col_sums[D_IDX] == ONE,
                f"Expected (y^T A)_D == 1, got {col_sums[D_IDX]} at {path}",
            )
            for j in range(N_VARS):
                if j != D_IDX:
                    require(
                        col_sums[j] >= ZERO,
                        f"Negative dual coefficient {col_sums[j]} on {VAR_NAMES[j]} at {path}",
                    )
            declared_bound = F(node["bound"])
            require(
                rhs_sum == declared_bound,
                f"Dual objective {rhs_sum} != declared bound {declared_bound} at {path}",
            )
            require(
                rhs_sum < target_D,
                f"Leaf bound {rhs_sum} is not strictly below D_target={target_D} at {path}",
            )

            # Check 2: Homogeneous Farkas infeasibility for {A x <= b, -D <= -target_D, x >= 0}
            farkas_lhs = list(col_sums)
            farkas_lhs[D_IDX] -= ONE
            require(
                all(c >= ZERO for c in farkas_lhs),
                f"Farkas LHS not non-negative at {path}",
            )
            farkas_rhs = rhs_sum - target_D
            require(
                farkas_rhs < ZERO,
                f"Farkas RHS {farkas_rhs} not strictly negative at {path}",
            )

            leaf_bounds.append(rhs_sum)
            return

        if ntype == "geo":
            require(
                set(node.keys()) == {"type", "I", "J", "K", "children"},
                f"Unexpected geo keys {set(node.keys())} at {path}",
            )
            branch_rows_list = geo_branches(node["I"], node["J"], node["K"])
        elif ntype == "ss":
            require(
                set(node.keys()) == {"type", "A", "pA", "B", "IB", "kB", "OC", "children"},
                f"Unexpected ss keys {set(node.keys())} at {path}",
            )
            branch_rows_list = ss_branches(
                node["A"], node["pA"], node["B"], node["IB"], node["kB"], node["OC"]
            )
        else:
            raise VerificationError(f"Unknown node type {ntype} at {path}")

        children = node["children"]
        require(
            isinstance(children, list) and len(children) == len(branch_rows_list),
            f"Expected {len(branch_rows_list)} children at {ntype} node {path}, got {len(children) if isinstance(children, list) else type(children)}",
        )
        for br_idx, (extra_rows, child) in enumerate(zip(branch_rows_list, children)):
            visit(child, rows + extra_rows, path + (br_idx,))

    visit(cert_data["tree"], base, ())
    require(counts["leaf"] > 0, "No leaves verified")
    if "leaves" in cert_data:
        require(counts["leaf"] == cert_data["leaves"], f"Leaf count mismatch: {counts['leaf']} vs {cert_data['leaves']}")
    max_bd = max(leaf_bounds)
    if "max_certified_D" in cert_data and override_target_D is None and override_base_rows is None:
        require(max_bd == F(cert_data["max_certified_D"]), f"max_certified_D mismatch: {max_bd} vs {cert_data['max_certified_D']}")
    require(max_bd < target_D, f"Max leaf bound {max_bd} >= target_D {target_D}")
    return {
        "counts": dict(counts),
        "max_depth": max_depth,
        "max_certified_D": max_bd,
        "target_D": target_D,
    }


def make_point_vector(coords_by_letter, totals_by_letter, D_val):
    """Build a 25-element exact Fraction vector x in VAR_NAMES order."""
    vals = {}
    for s in LETTERS:
        coords = coords_by_letter[s]
        require(len(coords) == 6, f"Expected 6 coordinates for {s}")
        for i in R6:
            vals[f"{s}{i}"] = F(coords[i - 1])
        vals[s] = F(totals_by_letter[s])
        vals[f"F{s}"] = max(
            sum(vals[f"{s}{i}"] for i in R6 if i % j == 0) for j in (2, 3, 5)
        )
    vals["D"] = F(D_val)
    return tuple(vals[name] for name in VAR_NAMES)


def eval_ss_direct(x_vec, A, pA, B, IB, kB, OC, use_cap=True):
    """Direct exact Fraction evaluation of the RHS of (**) at x_vec."""
    C = next(s for s in LETTERS if s not in (A, B))
    p = x_vec[POS[f"{A}{pA[0]}"]]
    q = x_vec[POS[f"{A}{pA[1]}"]]
    xA = x_vec[POS[A]]
    xB = x_vec[POS[B]]
    xC = x_vec[POS[C]]
    fA = xA - p - q
    fB = xB - sum(x_vec[POS[f"{B}{i}"]] for i in IB)
    wB = sum(i * x_vec[POS[f"{B}{i}"]] for i in R6 if i not in IB) + F(7) * (
        xB - sum(x_vec[POS[f"{B}{i}"]] for i in R6)
    )
    t1 = F(2) * p - wB
    t2 = F(2) * q - wB
    kappa = p + q + HALF * ((t1 if t1 > ZERO else ZERO) + (t2 if t2 > ZERO else ZERO))
    fC = sum(x_vec[POS[f"{C}{i}"]] for i in OC)
    wC = sum(i * x_vec[POS[f"{C}{i}"]] for i in OC)
    t3 = x_vec[POS[f"{B}{kB}"]] - wC
    delta = sum(x_vec[POS[f"{B}{i}"]] for i in IB if i != kB) + (t3 if t3 > ZERO else ZERO)
    if use_cap and not OC and IB in DIFF_CAPS:
        for idx in DIFF_CAPS[IB]:
            cap_val = F(2) * x_vec[POS[f"{B}{idx}"]]
            if cap_val < delta:
                delta = cap_val
    diag = fA + fB + xC
    off = fA + fB + fC + HALF * ((xC - fC) + delta + kappa)
    return diag if diag >= off else off


def verify_point_all_constraints(x_vec, check_full_oc=True, check_s3_order=True, check_ss=True):
    """Verify that x_vec >= 0 satisfies:
      - All base rows (B1)-(B3) (+ S3 ordering if check_s3_order)
      - All 2^18 = 262,144 geometric constraints (B4)
      - if check_ss: all v1 Thue and Determinant constraints, and all (**)
        constraints (both by direct RHS evaluation and by checking that at least one of the
        9 linear branch systems in ss_branches is satisfied).
    With check_ss=False only the root rows and (B4) are checked (the program of the reference
    paper); min_thue, min_det, min_ss0, min_ss_full are then returned as None.
    """
    require(all(v >= ZERO for v in x_vec), "Point has negative coordinate")
    base = build_base_rows(ONE)
    n_base = 22 if check_s3_order else 20
    for idx, (r_vec, rhs) in enumerate(base[:n_base]):
        require(dot(r_vec, x_vec) <= rhs, f"Point fails base row {idx}: {dot(r_vec, x_vec)} > {rhs}")

    D_val = x_vec[D_IDX]
    L_val = x_vec[POS["a"]] + x_vec[POS["b"]] + x_vec[POS["c"]]

    # All 2^18 geometric constraints (B4)
    opts = {}
    for s in LETTERS:
        opts[s] = [
            (
                I,
                sum(x_vec[POS[f"{s}{i}"]] for i in I),
                sum((i - 1) * x_vec[POS[f"{s}{i}"]] for i in I),
            )
            for I in SUBSETS
        ]
    min_geo = None
    for Ia, s0a, s1a in opts["a"]:
        for Ib, s0b, s1b in opts["b"]:
            for Ic, s0c, s1c in opts["c"]:
                v = max(L_val - (s0a + s0b + s0c), L_val - ONE + (s1a + s1b + s1c))
                if min_geo is None or v < min_geo[0]:
                    min_geo = (v, (Ia, Ib, Ic))
    require(min_geo[0] >= D_val, f"Point fails (B4) at {min_geo[1]}: {min_geo[0]} < {D_val}")

    # Also verify that for the tightest (B4) subset, at least one branch in geo_branches is satisfied
    g_brs = geo_branches(*min_geo[1])
    require(
        any(all(dot(rv, x_vec) <= rh for rv, rh in br) for br in g_brs),
        "geo_branches row check failed at tightest subset",
    )

    if not check_ss:
        return {"D": D_val, "min_geo": min_geo, "min_thue": None, "min_det": None, "min_ss0": None, "min_ss_full": None}

    # v1 Thue and Determinant bounds
    min_thue = min(
        L_val - sum(x_vec[POS[f"{s}{i}"]] + x_vec[POS[f"{t}{i}"]] for i in R6 if i % p == 0)
        for s, t in (("a", "b"), ("a", "c"), ("b", "c"))
        for p in range(2, 7)
    )
    min_det = min(
        L_val
        - x_vec[POS[f"{s}{p}"]]
        - x_vec[POS[f"{t}{q}"]]
        + min(x_vec[POS[f"{s}{p}"]] * F(1, q), x_vec[POS[f"{t}{q}"]] * F(1, p))
        for s, t in permutations(LETTERS, 2)
        for p in R6
        for q in R6
    )
    require(min_thue >= D_val and min_det >= D_val, f"Thue/Det failed: {min_thue}, {min_det}")

    # Check all O_C = empty instances (6 * 11 * 192 = 12,672 instances) via BOTH direct formula AND ss_branches
    min_ss0 = None
    for A, B in permutations(LETTERS, 2):
        for pA in COPRIME_PAIRS:
            for IB in NONEMPTY_SUBSETS:
                for kB in IB:
                    v = eval_ss_direct(x_vec, A, pA, B, IB, kB, (), use_cap=True)
                    if min_ss0 is None or v < min_ss0[0]:
                        min_ss0 = (v, (A, pA, B, IB, kB, ()))
    require(min_ss0[0] >= D_val, f"Point fails O_C=empty (**) at {min_ss0[1]}: {min_ss0[0]} < {D_val}")

    # Verify linear branch satisfaction on all 4,158 canonical O_C = empty instances
    for A, B in permutations(LETTERS, 2):
        for pA in COPRIME_PAIRS:
            for IB in NONEMPTY_SUBSETS:
                brs = ss_branches(A, pA, B, IB, IB[0], ())
                require(
                    any(all(dot(rv, x_vec) <= rh for rv, rh in br) for br in brs),
                    f"ss_branches row check failed at {(A, pA, B, IB, IB[0], ())}",
                )

    min_ss_full = min_ss0
    if check_full_oc:
        # Exhaustive scan of all 811,008 instances (including all 64 subsets O_C) in exact integer arithmetic
        den = math.lcm(*(v.denominator for v in x_vec))
        xv = [int(v * den) for v in x_vec]
        Dv = xv[D_IDX]
        best_num = None
        best_inst = None
        for C in LETTERS:
            fC_tab = [sum(xv[POS[f"{C}{i}"]] for i in OC) for OC in SUBSETS]
            wC_tab = [sum(i * xv[POS[f"{C}{i}"]] for i in OC) for OC in SUBSETS]
            for A, B in permutations(LETTERS, 2):
                if C in (A, B):
                    continue
                xA = xv[POS[A]]
                xB = xv[POS[B]]
                xC = xv[POS[C]]
                coordsB = [xv[POS[f"{B}{i}"]] for i in R6]
                tailB = 7 * (xB - sum(coordsB))
                for IB in NONEMPTY_SUBSETS:
                    sumIB = sum(coordsB[i - 1] for i in IB)
                    fB = xB - sumIB
                    wB = sum(i * coordsB[i - 1] for i in R6 if i not in IB) + tailB
                    for pA in COPRIME_PAIRS:
                        p = xv[POS[f"{A}{pA[0]}"]]
                        q = xv[POS[f"{A}{pA[1]}"]]
                        fA = xA - p - q
                        t1 = 2 * p - wB
                        t2 = 2 * q - wB
                        # 4 * (kappa / 2) = 2 * (p + q) + (t1_+ + t2_+) to stay in integers
                        half_kappa4 = 2 * (p + q) + ((t1 if t1 > 0 else 0) + (t2 if t2 > 0 else 0))
                        diag4 = 4 * (fA + fB + xC)
                        base_off4 = 4 * (fA + fB) + 2 * xC + half_kappa4
                        for kB in IB:
                            bkB = coordsB[kB - 1]
                            restB = sumIB - bkB
                            for oc_idx, OC in enumerate(SUBSETS):
                                t3 = bkB - wC_tab[oc_idx]
                                delta = restB + (t3 if t3 > 0 else 0)
                                if not OC and IB in DIFF_CAPS:
                                    for idx in DIFF_CAPS[IB]:
                                        cval = 2 * coordsB[idx - 1]
                                        if cval < delta:
                                            delta = cval
                                off4 = base_off4 + 2 * fC_tab[oc_idx] + 2 * delta
                                val4 = diag4 if diag4 >= off4 else off4
                                if best_num is None or val4 < best_num:
                                    best_num = val4
                                    best_inst = (A, pA, B, IB, kB, OC)
        min_ss_full = (F(best_num, 4 * den), best_inst)
        require(
            min_ss_full[0] >= D_val,
            f"Point fails full (**) at {min_ss_full[1]}: {min_ss_full[0]} < {D_val}",
        )
        # Also verify linear branch satisfaction on the tightest full-(**) instance (with non-empty O_C)
        brs_tight = ss_branches(*min_ss_full[1])
        require(
            any(all(dot(rv, x_vec) <= rh for rv, rh in br) for br in brs_tight),
            f"ss_branches row check failed at tightest full instance {min_ss_full[1]}",
        )

    return {
        "D": D_val,
        "min_geo": min_geo,
        "min_thue": min_thue,
        "min_det": min_det,
        "min_ss0": min_ss0,
        "min_ss_full": min_ss_full,
    }


def run_witness_checks():
    """Verify exact feasibility of the 213/359 full-space witness and 16/27, 7/12 symmetric witnesses."""
    t0 = time.time()
    # 1. Full-space witness D = 213/359 (ordered so a4+2a5 >= b4+2b5 >= c4+2c5:
    #    a = b = (30, 0, 43, 43, 0, 0)/359, alpha_a = alpha_b = 120/359;
    #    c = (0, 43, 43, 29, 0, 0)/359, alpha_c = 119/359)
    x_359 = make_point_vector(
        {
            "a": (F(30, 359), ZERO, F(43, 359), F(43, 359), ZERO, ZERO),
            "b": (F(30, 359), ZERO, F(43, 359), F(43, 359), ZERO, ZERO),
            "c": (ZERO, F(43, 359), F(43, 359), F(29, 359), ZERO, ZERO),
        },
        {"a": F(120, 359), "b": F(120, 359), "c": F(119, 359)},
        F(213, 359),
    )
    res_359 = verify_point_all_constraints(x_359, check_full_oc=True, check_s3_order=True)
    require(res_359["min_geo"][0] == F(213, 359), f"Expected geo min 213/359, got {res_359['min_geo'][0]}")
    require(res_359["min_ss0"][0] == F(213, 359), f"Expected ss0 min 213/359, got {res_359['min_ss0'][0]}")
    require(res_359["min_ss_full"][0] == F(213, 359), f"Expected ss_full min 213/359, got {res_359['min_ss_full'][0]}")
    # Also explicitly check a non-empty O_C instance at x_359: (A='c', pA=(2,3), B='a', IB=(3,4), kB=3, OC=(1,))
    rhs_oc1 = eval_ss_direct(x_359, "c", (2, 3), "a", (3, 4), 3, (1,), use_cap=True)
    require(rhs_oc1 == F(227, 359) >= F(213, 359), f"Unexpected O_C={{1}} value: {rhs_oc1}")
    brs_oc1 = ss_branches("c", (2, 3), "a", (3, 4), 3, (1,))
    require(
        any(all(dot(rv, x_359) <= rh for rv, rh in br) for br in brs_oc1),
        "ss_branches failed on O_C={1} tight instance",
    )
    print(
        f"PASS [Witness 213/359]: exact feasible under (B1)-(B3), all 2^18 (B4) (min={res_359['min_geo'][0]}), "
        f"Thue ({res_359['min_thue']}), Det ({res_359['min_det']}), and all 811,008 (**) "
        f"instances (min={res_359['min_ss_full'][0]} at {res_359['min_ss_full'][1]}) ({time.time()-t0:.2f}s)"
    )

    # 2. Symmetric subspace witness D = 16/27 for O_C = empty subfamily:
    #    a = b = c = (6, 0, 12, 8, 0, 0)/81, alpha = 27/81 = 1/3 (tail = 1/81)
    x_sym_16_27 = make_point_vector(
        {s: (F(6, 81), ZERO, F(12, 81), F(8, 81), ZERO, ZERO) for s in LETTERS},
        {s: F(1, 3) for s in LETTERS},
        F(16, 27),
    )
    res_sym0 = verify_point_all_constraints(x_sym_16_27, check_full_oc=False, check_s3_order=True)
    require(
        res_sym0["min_geo"][0] == F(16, 27) and res_sym0["min_ss0"][0] == F(97, 162) >= F(16, 27),
        f"Unexpected sym_16_27 bounds: geo={res_sym0['min_geo'][0]}, ss0={res_sym0['min_ss0'][0]}",
    )

    # Also verify the old-(*) symmetric witness (11, 0, 24, 16, 3, 0)/162 at D = 16/27
    # satisfies the root rows R(1), all 2^18 constraints (B4) (smallest right-hand side 16/27)
    # and the 24 old (*) constraints (smallest right-hand side 49/81); the difference refinement with IB=(3,5)
    # cuts it to 95/162, shifting the O_C=empty symmetric optimum to x_sym_16_27 = (6, 0, 12, 8, 0, 0)/81.
    x_sym_old = make_point_vector(
        {s: (F(11, 162), ZERO, F(24, 162), F(16, 162), F(3, 162), ZERO) for s in LETTERS},
        {s: F(1, 3) for s in LETTERS},
        F(16, 27),
    )
    res_sym_old = verify_point_all_constraints(x_sym_old, check_full_oc=False, check_s3_order=True, check_ss=False)
    require(res_sym_old["min_geo"][0] == F(16, 27), f"Expected (B4) min 16/27 at the (*) symmetric point, got {res_sym_old['min_geo'][0]}")
    min_old_star = min(
        eval_ss_direct(x_sym_old, A, pA, B, IB, IB[0], (), use_cap=True)
        for A, B in permutations(LETTERS, 2)
        for pA in ((2, 3), (3, 4))
        for IB in ((2, 3), (3, 4))
    )
    require(min_old_star == F(49, 81) >= F(16, 27), f"Expected old (*) >= 16/27, got {min_old_star}")

    # 3. Symmetric subspace witness D = 7/12 for full (**) family:
    #    a = b = c = (3, 0, 7, 6, 0, 0)/48, alpha = 1/3
    x_sym_7_12 = make_point_vector(
        {s: (F(3, 48), ZERO, F(7, 48), F(6, 48), ZERO, ZERO) for s in LETTERS},
        {s: F(1, 3) for s in LETTERS},
        F(7, 12),
    )
    res_sym_full = verify_point_all_constraints(x_sym_7_12, check_full_oc=True, check_s3_order=True)
    require(
        res_sym_full["min_geo"][0] >= F(7, 12) and res_sym_full["min_ss_full"][0] >= F(7, 12),
        f"Expected >= 7/12, got {res_sym_full['min_ss_full'][0]}",
    )
    print(
        f"PASS [Symmetric Witnesses]: D=16/27 feasible for R(1), all (B4) and the 24 old (*) "
        f"(geo={res_sym_old['min_geo'][0]}, (*)={min_old_star}) and for the O_C=empty subfamily "
        f"(geo={res_sym0['min_geo'][0]}, ss0={res_sym0['min_ss0'][0]}); "
        f"D=7/12 feasible for full (**) family (geo={res_sym_full['min_geo'][0]}, ss_full={res_sym_full['min_ss_full'][0]})."
    )

    # 4. Budget-1 witness for the program of the reference paper (root rows + all (B4), no collision
    #    inequality): a = b = (0, 1, 1, 0, 1, 0)/10, alpha_a = alpha_b = 3/10; c = (0, 2, 2, 0, 0, 0)/10,
    #    alpha_c = 2/5; D = 3/5.  Exactly feasible with smallest (B4) right-hand side 3/5, so that program
    #    has value exactly 3/5 at budget 1 (it is bounded by 3/5 by Proposition 6.1 of the reference paper).
    #    The same point is cut to 11/20 by the 24 constraints (*) and by the O_C=empty instances of (**).
    x_blt = make_point_vector(
        {
            "a": (ZERO, F(1, 10), F(1, 10), ZERO, F(1, 10), ZERO),
            "b": (ZERO, F(1, 10), F(1, 10), ZERO, F(1, 10), ZERO),
            "c": (ZERO, F(2, 10), F(2, 10), ZERO, ZERO, ZERO),
        },
        {"a": F(3, 10), "b": F(3, 10), "c": F(2, 5)},
        F(3, 5),
    )
    res_blt = verify_point_all_constraints(x_blt, check_full_oc=False, check_s3_order=True, check_ss=False)
    require(res_blt["min_geo"][0] == F(3, 5), f"Expected (B4) min 3/5 at the budget-1 witness, got {res_blt['min_geo'][0]}")
    min_blt_star = min(
        eval_ss_direct(x_blt, A, pA, B, IB, IB[0], (), use_cap=True)
        for A, B in permutations(LETTERS, 2)
        for pA in ((2, 3), (3, 4))
        for IB in ((2, 3), (3, 4))
    )
    min_blt_ss0 = min(
        eval_ss_direct(x_blt, A, pA, B, IB, kB, (), use_cap=True)
        for A, B in permutations(LETTERS, 2)
        for pA in COPRIME_PAIRS
        for IB in NONEMPTY_SUBSETS
        for kB in IB
    )
    require(min_blt_star == F(11, 20) and min_blt_ss0 == F(11, 20), f"Expected (*)/(**) cut to 11/20 at the budget-1 witness, got {min_blt_star}, {min_blt_ss0}")
    print(
        f"PASS [Budget-1 witness of the reference program]: D=3/5 feasible for R(1) and all 2^18 (B4) "
        f"(min={res_blt['min_geo'][0]}); cut by (*) to {min_blt_star} and by O_C=empty (**) to {min_blt_ss0}."
    )


def find_first_leaf(node):
    if node["type"] == "leaf":
        return node
    for ch in node["children"]:
        res = find_first_leaf(ch)
        if res is not None:
            return res
    return None


def find_first_internal(node, kind=None):
    if node["type"] == "leaf":
        return None
    if kind is None or node["type"] == kind:
        return node
    for ch in node["children"]:
        res = find_first_internal(ch, kind)
        if res is not None:
            return res
    return None


def run_fault_injections(cert_data):
    """Run fault-injection tests (covering multiplier tampering, constraint deletion,
    target constant modification, and parameter tampering) and confirm all are rejected.
    """
    results = []

    # Fault 1a: Tamper with a dual multiplier in a leaf (without updating declared bound)
    c1a = copy.deepcopy(cert_data)
    leaf1a = find_first_leaf(c1a["tree"])
    first_key = next(iter(leaf1a["y"]))
    leaf1a["y"][first_key] = str(F(leaf1a["y"][first_key]) + F(1, 1000))
    try:
        verify_certificate(c1a)
        raise RuntimeError("Fault 1a (tampered multiplier) was NOT rejected!")
    except VerificationError as e:
        results.append(("Fault 1a (one multiplier perturbed, y_i -> y_i + 1/1000)", f"REJECTED: {e}"))

    # Fault 1b: Decrease a dual multiplier AND sync declared bound (must fail Farkas LHS check)
    c1b = copy.deepcopy(cert_data)
    leaf1b = find_first_leaf(c1b["tree"])
    k1b = next(iter(leaf1b["y"]))
    leaf1b["y"][k1b] = str(F(leaf1b["y"][k1b]) - F(1, 1000))
    if k1b == "0":
        leaf1b["bound"] = str(F(leaf1b["bound"]) - F(1, 1000))
    try:
        verify_certificate(c1b)
        raise RuntimeError("Fault 1b (tampered multiplier with synced bound) was NOT rejected!")
    except VerificationError as e:
        results.append(("Fault 1b (multiplier lowered with matching declared bound; Farkas sign condition broken)", f"REJECTED: {e}"))

    # Fault 2a: Delete/zero a base constraint row (replace Row 19 with a zero row so indices stay valid)
    base_zeroed = build_base_rows(ONE)
    base_zeroed[19] = (tuple(ZERO for _ in range(N_VARS)), ZERO)
    try:
        verify_certificate(cert_data, override_base_rows=base_zeroed)
        raise RuntimeError("Fault 2a (deleted/zeroed base constraint Row 19) was NOT rejected!")
    except VerificationError as e:
        results.append(("Fault 2a (root row 19 set to zero)", f"REJECTED: {e}"))

    # Fault 2b: Delete a base constraint row from the list
    base_minus_1 = build_base_rows(ONE)
    del base_minus_1[19]
    try:
        verify_certificate(cert_data, override_base_rows=base_minus_1)
        raise RuntimeError("Fault 2b (removed base constraint Row 19) was NOT rejected!")
    except VerificationError as e:
        results.append(("Fault 2b (root row 19 removed from the row table)", f"REJECTED: {e}"))

    # Fault 2c: Delete a child branch from an internal node
    c2c = copy.deepcopy(cert_data)
    internal_node = find_first_internal(c2c["tree"], "ss") or find_first_internal(c2c["tree"])
    internal_node["children"].pop()
    try:
        verify_certificate(c2c)
        raise RuntimeError("Fault 2c (deleted branch child) was NOT rejected!")
    except VerificationError as e:
        results.append(("Fault 2c (one child of an internal node removed)", f"REJECTED: {e}"))

    # Fault 3: Change target constant D_target to 213/359 (feasible lower bound)
    try:
        verify_certificate(cert_data, override_target_D=F(213, 359))
        raise RuntimeError("Fault 3 (lowered D_target to 213/359) was NOT rejected!")
    except VerificationError as e:
        results.append(("Fault 3 (target constant lowered to D_target = 213/359)", f"REJECTED: {e}"))

    # Fault 4: Tamper with an (**) node parameter (make pA non-coprime [2, 4])
    c4 = copy.deepcopy(cert_data)
    ss_node = find_first_internal(c4["tree"], "ss")
    if ss_node is not None:
        ss_node["pA"] = [2, 4]
        try:
            verify_certificate(c4)
            raise RuntimeError("Fault 4 (non-coprime pA=[2,4]) was NOT rejected!")
        except VerificationError as e:
            results.append(("Fault 4 (node label pA=[2,4], not coprime)", f"REJECTED: {e}"))

    for name, msg in results:
        print(f"PASS [{name}]: {msg}")
    return results


def main():
    cert_path = Path(__file__).with_name("cert_starstar.json")
    if len(sys.argv) > 1:
        cert_path = Path(sys.argv[1])
    t0 = time.time()
    cert_data = load_certificate(cert_path)
    info = verify_certificate(cert_data)
    cert_time = time.time() - t0
    target_D = info["target_D"]
    max_D = info["max_certified_D"]
    gap = target_D - F(213, 359)
    max_gap = max_D - F(213, 359)
    print(
        f"PASS [Certificate {cert_path.name}]: {info['counts']} nodes, max_depth={info['max_depth']}, "
        f"max_certified_D = {max_D} ({float(max_D):.9f}) < D_target = {target_D} ({float(target_D):.9f}) "
        f"verified in {cert_time:.2f}s"
    )
    print(
        f"  D_target - 213/359 = {gap} ({float(gap):.9f}); "
        f"max_certified_D - 213/359 = {max_gap} ({float(max_gap):.9f})"
    )
    run_witness_checks()
    run_fault_injections(cert_data)
    print(f"ALL CHECKS PASSED in {time.time() - t0:.2f}s.")


if __name__ == "__main__":
    main()
