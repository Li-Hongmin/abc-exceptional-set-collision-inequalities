"""Independent exact checker for the lambda-curve certificates (fractions.Fraction only).

Standard library only.  Rebuilds every row from the formulas of the manuscript
(Sections 2, 4, 5) with the budget row  a+b+c <= lambda, walks the tree, and
checks at each leaf (rows = root rows + branch rows on the path):

    y_i > 0,   (y^T A)_D = 1,   (y^T A)_v >= 0 (v != D),   y^T b = bound <= D*.

Every check raises VerificationError explicitly (no assert statements), so the
verifier cannot be disabled by running the interpreter with -O.

It also checks that the recorded point has non-negative coordinates and is exactly feasible for the root rows,
all 24 collision constraints (*) and all 2^18 constraints (B4) with D = D*,
so that D* is the exact value of the disjunctive program at this lambda.

Parametric envelope: only row 0 depends on lambda, so with the SAME tree and
multipliers, every leaf certifies  D <= bound_leaf + y_leaf[0]*(mu - lambda)
for every budget mu.  The checker reports  E_lambda(mu) = max over leaves  of
that affine function, which is a rigorous upper bound for D*(mu).

Usage:
    python3 check_lambda.py cert_lambda_0p70.json [cert_lambda_0p75.json ...]
    python3 check_lambda.py --envelope   (all certs in this directory; prints envelope table)
"""
from fractions import Fraction as F
from itertools import permutations
import json
import sys
from pathlib import Path

ZERO = F(0)


class VerificationError(Exception):
    """Raised when any certificate check fails."""


def require(cond, msg):
    if not cond:
        raise VerificationError(msg)

NAMES = [f"{s}{i}" for s in "abc" for i in range(1, 7)]
# interface order shared with the generator: a1..a6, a, b1..b6, b, c1..c6, c, Fa, Fb, Fc, D
VAR = []
for s in "abc":
    VAR += [f"{s}{i}" for i in range(1, 7)] + [s]
VAR += ["Fa", "Fb", "Fc", "D"]
IX = {v: k for k, v in enumerate(VAR)}
NV = len(VAR)
D = IX["D"]


def row(terms, rhs):
    r = [ZERO] * NV
    for k, v in terms.items():
        r[IX[k]] += F(v)
    return r, F(rhs)


def root_rows(lam):
    """(B1)-(B3) linearised + ordering (5.1); row 0 is the budget row."""
    rows = [row({"a": 1, "b": 1, "c": 1}, lam)]
    for s in "abc":
        t = {f"{s}{i}": 1 for i in range(1, 7)}
        t[s] = -1
        rows.append(row(t, 0))  # sum_{i<=6} s_i <= s
        t = {f"{s}{i}": -(7 - i) for i in range(1, 7)}
        t[s] = 7
        rows.append(row(t, 1))  # 7s - sum (7-i) s_i <= 1
    rows.append(row({"D": 1, "a": -1, "b": -1}, 0))
    rows.append(row({"D": 1, "a": -1, "c": -1}, 0))
    rows.append(row({"D": 1, "b": -1, "c": -1}, 0))
    for s in "abc":
        for j in (2, 3, 5):
            t = {f"{s}{i}": 1 for i in range(1, 7) if i % j == 0}
            t[f"F{s}"] = -1
            rows.append(row(t, 0))  # F_s >= sum_{j|i} s_i
    rows.append(row({"Fa": 1, "Fb": 1, "Fc": 1, "a": -4, "b": -4, "c": -4, "D": 6}, 0))
    rows.append(row({"b4": 1, "b5": 2, "a4": -1, "a5": -2}, 0))
    rows.append(row({"c4": 1, "c5": 2, "b4": -1, "b5": -2}, 0))
    require(len(rows) == 22, "root system must have 22 rows")
    return rows


def geo_rows(I, J, K, br):
    """(B4) branch br: 0 -> D <= L - Sigma0 ; 1 -> D <= L - 1 + Sigma1."""
    t = {"D": 1, "a": -1, "b": -1, "c": -1}
    for s, S in (("a", I), ("b", J), ("c", K)):
        for i in S:
            t[f"{s}{i}"] = t.get(f"{s}{i}", 0) + (1 if br == 0 else -(i - 1))
    return [row(t, 0 if br == 0 else -1)]


def w_terms(B, pB):
    """w_B = sum_{i<=6, i not in pB} i*B_i + 7(B - sum_{i<=6} B_i), as a linear form."""
    t = {B: F(7)}
    for i in range(1, 7):
        t[f"{B}{i}"] = F(-7) if i in pB else F(-(7 - i))
    return t


def tl_rows(A, pA, B, pB, br):
    """(*) branch br.  br=0: D <= f_out + alpha_C.
    br=1..4: sign quadrant (sig_p, sig_q) in {0,1}^2 for t1 = 2p - w_B, t2 = 2q - w_B
    (sig=1 means the term is on its positive side and enters kappa), then the two rows
    D <= f_out + (alpha_C + 2*cap + kappa)/2 for cap in {r, s}."""
    C = ({"a", "b", "c"} - {A, B}).pop()
    pn, qn = f"{A}{pA[0]}", f"{A}{pA[1]}"
    rn, sn = f"{B}{pB[0]}", f"{B}{pB[1]}"
    fout = {A: 1, B: 1, pn: -1, qn: -1, rn: -1, sn: -1}  # f_out as linear form
    if br == 0:
        t = {"D": 1, C: -1}
        for k, v in fout.items():
            t[k] = t.get(k, 0) - v
        return [row(t, 0)]
    sig_p, sig_q = (br - 1) // 2, (br - 1) % 2
    w = w_terms(B, pB)
    out = []
    for coord, sig in ((pn, sig_p), (qn, sig_q)):
        # sig=0:  2*coord - w <= 0 ;  sig=1:  w - 2*coord <= 0
        t = {}
        for k, v in w.items():
            t[k] = (-v if sig == 0 else v)
        t[coord] = t.get(coord, ZERO) + (F(2) if sig == 0 else F(-2))
        out.append(row(t, 0))
    for cap in (rn, sn):
        # D - f_out - alpha_C/2 - cap - kappa/2 <= 0 ,  kappa = p + q + (sig_p*(2p-w) + sig_q*(2q-w))/2
        t = {"D": F(1), C: F(-1, 2), cap: F(-1)}
        for k, v in fout.items():
            t[k] = t.get(k, ZERO) - v
        t[pn] = t.get(pn, ZERO) - F(1, 2) - F(sig_p, 2)
        t[qn] = t.get(qn, ZERO) - F(1, 2) - F(sig_q, 2)
        if sig_p + sig_q:
            for k, v in w.items():
                t[k] = t.get(k, ZERO) + F(sig_p + sig_q, 4) * v
        out.append(row(t, 0))
    return out


# ---------------------------------------------------------------- exact evaluation at a point
def point_values(pt):
    x = {k: F(pt.get(k, "0")) for k in VAR}
    require(all(v >= ZERO for v in x.values()), "recorded point has a negative coordinate")
    return x


def check_root_rows(x, lam):
    for r, b in root_rows(lam):
        if sum(r[j] * x[VAR[j]] for j in range(NV)) > b:
            return False
    return True


def tl_ok(x, A, pA, B, pB):
    C = ({"a", "b", "c"} - {A, B}).pop()
    p, q = x[f"{A}{pA[0]}"], x[f"{A}{pA[1]}"]
    r, s = x[f"{B}{pB[0]}"], x[f"{B}{pB[1]}"]
    w = sum(i * x[f"{B}{i}"] for i in range(1, 7) if i not in pB) + 7 * (x[B] - sum(x[f"{B}{i}"] for i in range(1, 7)))
    kappa = p + q + (max(ZERO, 2 * p - w) + max(ZERO, 2 * q - w)) / 2
    fout = x[A] - p - q + x[B] - r - s
    return x["D"] <= fout + max(x[C], (x[C] + min(r + s, 2 * r, 2 * s) + kappa) / 2)


def geo_all_ok(x):
    L = x["a"] + x["b"] + x["c"]
    subsets = [tuple(i for i in range(1, 7) if m >> (i - 1) & 1) for m in range(64)]
    per = {}
    for s in "abc":
        per[s] = [(sum(x[f"{s}{i}"] for i in S), sum((i - 1) * x[f"{s}{i}"] for i in S)) for S in subsets]
    Dv = x["D"]
    for a0, a1 in per["a"]:
        for b0, b1 in per["b"]:
            for c0, c1 in per["c"]:
                if Dv > L - a0 - b0 - c0 and Dv > L - 1 + a1 + b1 + c1:
                    return False
    return True


# ---------------------------------------------------------------- tree walk
def check_cert(path, verbose=True):
    cert = json.load(open(path))
    lam = F(cert["lambda"])
    Dstar = F(cert["Dstar"])
    base = root_rows(lam)
    stats = {"leaves": 0, "max_bound": ZERO, "max_slope": ZERO, "leaf_affine": [], "max_depth": 0, "geo_nodes": 0, "tl_nodes": 0}

    def walk(node, rows, depth):
        stats["max_depth"] = max(stats["max_depth"], depth)
        t = node["type"]
        if t == "leaf":
            y = {int(k): F(v) for k, v in node["y"].items()}
            require(bool(y) and all(v > 0 for v in y.values()), "multipliers must be > 0")
            require(all(0 <= i < len(rows) for i in y), "multiplier index out of range")
            for j in range(NV):
                col = sum(v * rows[i][0][j] for i, v in y.items())
                if j == D:
                    require(col == 1, f"D coefficient {col} != 1")
                else:
                    require(col >= 0, f"negative coefficient {col} on {VAR[j]}")
            bound = sum(v * rows[i][1] for i, v in y.items())
            require(bound == F(node["bound"]), f"declared bound {node['bound']} != y^T b = {bound}")
            require(bound <= Dstar, f"leaf bound {bound} > D* {Dstar}")
            slope = y.get(0, ZERO)  # multiplier of the budget row  a+b+c <= lambda
            stats["leaves"] += 1
            stats["max_bound"] = max(stats["max_bound"], bound)
            stats["max_slope"] = max(stats["max_slope"], slope)
            stats["leaf_affine"].append((bound, slope))
        elif t == "geo":
            I, J, K = tuple(node["I"]), tuple(node["J"]), tuple(node["K"])
            require(all(all(1 <= i <= 6 for i in S) and len(set(S)) == len(S) for S in (I, J, K)), "illegal (B4) index set")
            require(len(node["children"]) == 2, "(B4) node must have 2 children")
            stats["geo_nodes"] += 1
            for br in (0, 1):
                walk(node["children"][br], rows + geo_rows(I, J, K, br), depth + 1)
        elif t == "tl":
            A, pA, B, pB = node["A"], tuple(node["pA"]), node["B"], tuple(node["pB"])
            require(A in "abc" and B in "abc" and A != B, "illegal letters in (*) node")
            require(pA in ((2, 3), (3, 4)) and pB in ((2, 3), (3, 4)), "illegal exponent pairs in (*) node")
            require(len(node["children"]) == 5, "(*) node must have 5 children")
            stats["tl_nodes"] += 1
            for br in range(5):
                walk(node["children"][br], rows + tl_rows(A, pA, B, pB, br), depth + 1)
        else:
            raise VerificationError(f"unknown node type {t!r}")

    sys.setrecursionlimit(100000)
    walk(cert["tree"], list(base), 0)
    require(stats["max_bound"] == Dstar, f"max leaf bound {stats['max_bound']} != claimed D* {Dstar}")
    # exact feasibility of the attained point
    x = point_values(cert["attained_point"])
    attained = x["D"] == Dstar and check_root_rows(x, lam)
    # trees without (*) nodes certify the BLT-v2-only program; its optimum need not satisfy (*)
    base_only = stats["tl_nodes"] == 0
    if not base_only:
        attained = attained and all(tl_ok(x, A, pA, B, pB) for A, B in permutations("abc", 2) for pA in ((2, 3), (3, 4)) for pB in ((2, 3), (3, 4)))
    attained = attained and geo_all_ok(x)
    stats["attained"] = attained
    stats["base_only"] = base_only
    stats["lambda"] = lam
    stats["Dstar"] = Dstar
    if verbose:
        print(
            f"{Path(path).name}: lambda={lam} D*={Dstar} ({float(Dstar):.9f}) leaves={stats['leaves']} "
            f"(geo nodes {stats['geo_nodes']}, tl nodes {stats['tl_nodes']}, depth {stats['max_depth']}) "
            f"certificate PASS{' [BLT v2 rows only, no (*) nodes]' if base_only else ''}; attained by exact point: {attained}; max slope dD/dlambda over leaves = {stats['max_slope']} ({float(stats['max_slope']):.4f})"
        )
    return stats


def envelope(stats, mu):
    """Rigorous bound  E_lambda(mu) = max_leaf (bound + slope*(mu - lambda))  from one tree."""
    lam = stats["lambda"]
    return max(b + s * (mu - lam) for b, s in stats["leaf_affine"])


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    here = Path(__file__).parent
    if "--envelope" in sys.argv or not args:
        args = sorted(str(p) for p in here.glob("cert_lambda_*.json"))
    all_stats = [check_cert(a) for a in args]
    if "--envelope" in sys.argv and len(all_stats) >= 2:
        all_stats.sort(key=lambda s: s["lambda"])
        print("\nParametric envelope between grid points (upper bounds valid for every mu in the interval):")
        print("  interval        | mu (midpoint) | E_left(mu) | E_right(mu) | min       | max(D*_left, D*_right)")
        for s1, s2 in zip(all_stats, all_stats[1:]):
            mu = (s1["lambda"] + s2["lambda"]) / 2
            e1, e2 = envelope(s1, mu), envelope(s2, mu)
            print(f"  [{float(s1['lambda']):.2f}, {float(s2['lambda']):.2f}]    | {float(mu):.3f}         | {float(e1):.6f}   | {float(e2):.6f}    | {float(min(e1, e2)):.6f}  | {float(max(s1['Dstar'], s2['Dstar'])):.6f}")
