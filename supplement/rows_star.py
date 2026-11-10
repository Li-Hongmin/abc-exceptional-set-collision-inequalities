"""Row formulas of the program with the 24 collision inequalities (*) (standard library only).

This module is imported by bb_lambda.py only.  It builds the 22 root rows
R(1) (the budget row is replaced by bb_lambda.py for other budgets), the two
rows of a geometry-of-numbers disjunction (B4), and the rows of the five-branch
linearization of the inequality (*) described in Section 5 of the paper.
"""
from fractions import Fraction as F

ZERO = F(0)

VAR_NAMES = (
    [f"a{i}" for i in range(1, 7)]
    + ["a"]
    + [f"b{i}" for i in range(1, 7)]
    + ["b"]
    + [f"c{i}" for i in range(1, 7)]
    + ["c"]
    + ["Fa", "Fb", "Fc", "D"]
)
IDX = {name: i for i, name in enumerate(VAR_NAMES)}
N_VARS = len(VAR_NAMES)
D_IDX = IDX["D"]


def _make_row(terms, rhs):
    row = [ZERO] * N_VARS
    for k, v in terms.items():
        row[IDX[k]] += F(v)
    return (tuple(row), F(rhs))



def _build_v2_base_rows():
    """Return the 22 pure BLT v2 base linear inequalities (no Thue/Det) + WLOG S3 ordering."""
    rows = []
    rows.append(_make_row({"a": 1, "b": 1, "c": 1}, 1))
    for s in "abc":
        t = {f"{s}{i}": 1 for i in range(1, 7)}
        t[s] = -1
        rows.append(_make_row(t, 0))
        t2 = {f"{s}{i}": -(7 - i) for i in range(1, 7)}
        t2[s] = 7
        rows.append(_make_row(t2, 1))
    rows.append(_make_row({"D": 1, "a": -1, "b": -1}, 0))
    rows.append(_make_row({"D": 1, "a": -1, "c": -1}, 0))
    rows.append(_make_row({"D": 1, "b": -1, "c": -1}, 0))
    for s in "abc":
        for j in (2, 3, 5):
            t = {f"{s}{i}": 1 for i in range(1, 7) if i % j == 0}
            t[f"F{s}"] = -1
            rows.append(_make_row(t, 0))
    rows.append(
        _make_row({"Fa": 1, "Fb": 1, "Fc": 1, "a": -4, "b": -4, "c": -4, "D": 6}, 0)
    )
    # WLOG S3 symmetry breaking on the S3-invariant problem: a4 + 2*a5 >= b4 + 2*b5 >= c4 + 2*c5
    rows.append(_make_row({"b4": 1, "b5": 2, "a4": -1, "a5": -2}, 0))
    rows.append(_make_row({"c4": 1, "c5": 2, "b4": -1, "b5": -2}, 0))
    return rows


def _cond_to_rows(cond):
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
            return [_make_row(t, 0)]
        else:
            t = {"D": 1, "a": -1, "b": -1, "c": -1}
            for i in I:
                t[f"a{i}"] = t.get(f"a{i}", 0) - (i - 1)
            for i in J:
                t[f"b{i}"] = t.get(f"b{i}", 0) - (i - 1)
            for i in K:
                t[f"c{i}"] = t.get(f"c{i}", 0) - (i - 1)
            return [_make_row(t, -1)]
    elif kind == "tl":
        _, A, pA, B, pB, br = cond
        C = ({"a", "b", "c"} - {A, B}).pop()
        if br == 0:
            t = {
                "D": 1,
                A: -1,
                B: -1,
                C: -1,
                f"{A}{pA[0]}": 1,
                f"{A}{pA[1]}": 1,
                f"{B}{pB[0]}": 1,
                f"{B}{pB[1]}": 1,
            }
            return [_make_row(t, 0)]
        else:
            sig_p = (br - 1) // 2
            sig_q = (br - 1) % 2
            w_terms = {B: F(7)}
            for i in range(1, 7):
                w_terms[f"{B}{i}"] = -F(7) if i in pB else -F(7 - i)
            out_rows = []
            tp = {k: (-v if sig_p == 0 else v) for k, v in w_terms.items()}
            tp[f"{A}{pA[0]}"] = tp.get(f"{A}{pA[0]}", ZERO) + (
                F(2) if sig_p == 0 else -F(2)
            )
            out_rows.append(_make_row(tp, 0))
            tq = {k: (-v if sig_q == 0 else v) for k, v in w_terms.items()}
            tq[f"{A}{pA[1]}"] = tq.get(f"{A}{pA[1]}", ZERO) + (
                F(2) if sig_q == 0 else -F(2)
            )
            out_rows.append(_make_row(tq, 0))
            for cap_coord in pB:
                t = {"D": F(1), A: -F(1), B: -F(1), C: -F(1, 2)}
                t[f"{A}{pA[0]}"] = (
                    t.get(f"{A}{pA[0]}", ZERO)
                    + F(1)
                    - F(1, 2) * (F(1) + F(sig_p))
                )
                t[f"{A}{pA[1]}"] = (
                    t.get(f"{A}{pA[1]}", ZERO)
                    + F(1)
                    - F(1, 2) * (F(1) + F(sig_q))
                )
                t[f"{B}{pB[0]}"] = t.get(f"{B}{pB[0]}", ZERO) + F(1)
                t[f"{B}{pB[1]}"] = t.get(f"{B}{pB[1]}", ZERO) + F(1)
                t[f"{B}{cap_coord}"] = t.get(f"{B}{cap_coord}", ZERO) - F(1)
                if sig_p + sig_q > 0:
                    scale_w = F(sig_p + sig_q, 4)
                    for k, v in w_terms.items():
                        t[k] = t.get(k, ZERO) + scale_w * v
                out_rows.append(_make_row(t, 0))
            return out_rows
    raise ValueError(f"Unknown condition kind: {kind}")


