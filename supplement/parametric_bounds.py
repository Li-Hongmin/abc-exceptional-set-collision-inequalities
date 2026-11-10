"""Parametric (budget-dependent) bounds read off the verified trees (Fraction only).

Only the budget row  a+b+c <= lambda  depends on lambda.  A leaf with multipliers y
and bound  y^T b(lambda)  therefore certifies  D <= bound + y_0 (mu - lambda)  for
every budget mu, where y_0 is the multiplier of the budget row.  This script

  1. verifies each lambda-curve tree with check_lambda.check_cert and prints, for
     consecutive grid points lambda_k < lambda_{k+1}, the values E_k(lambda_{k+1})
     needed in the proof of Corollary 1.3;
  2. verifies the (**) tree with check_starstar.verify_certificate and prints the
     largest budget multiplier, the largest mu with  E_1(mu) <= 3/5, and E_1(mu) at a
     few budgets mu > 1;
  3. prints the table of Section 6 for
        beta(mu) = min(E_k(mu), E_{k+1}(mu), D*(lambda_{k+1}))   on [lambda_k, lambda_{k+1}],
        beta(mu) = min(E_0.90(mu), E_1(mu))                       on [0.90, 1],
        beta(mu) = E_1(mu)                                        on [1, 1.10],
     at steps of 0.01 (and 0.025), together with the comparison function of
     Corollary 1.3(ii),
        g(mu) = min((23 mu+3)/40, 2 mu/3, 3/5)  for mu < 1,
        g(mu) = min((23 mu+3)/40, 2 mu/3)       for mu >= 1
     (the exponent 3/5 of the reference paper is available for lambda < 1 only);
  4. checks  beta(mu) < g(mu)  in exact arithmetic at every breakpoint of beta and of g
     in [0.70, 1.10] (both functions are piecewise affine, so this covers the whole
     interval) and at the left limit mu -> 1-, and prints the smallest gap.

Every check raises an exception explicitly (no assert statements).

Usage:
    python3 parametric_bounds.py [certificate_directory]      (default: the directory of this file)
"""
from fractions import Fraction as F
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_lambda as ck  # noqa: E402
import check_starstar as cs  # noqa: E402

sys.setrecursionlimit(100000)


class ParametricError(Exception):
    """Raised when a verification step of this script fails."""


def require(cond, msg):
    if not cond:
        raise ParametricError(msg)


def leaf_affine_starstar(tree):
    out = []

    def walk(n):
        if n["type"] == "leaf":
            out.append((F(n["bound"]), F(n["y"].get("0", "0"))))
        else:
            for c in n["children"]:
                walk(c)

    walk(tree)
    return out


def envelope(leaf_affine, lam, mu):
    return max(b + s * (mu - lam) for b, s in leaf_affine)


def g_compare(mu):
    """Comparison function of Corollary 1.3(ii)."""
    v = min((23 * mu + 3) / 40, 2 * mu / 3)
    return min(v, F(3, 5)) if mu < 1 else v


def envelope_breakpoints(leaf_affine, lam, lo, hi):
    """Breakpoints in (lo, hi) of  mu -> max_leaf (bound + slope (mu - lam))  (upper hull of lines)."""
    best = {}
    for b, s in leaf_affine:
        c = b - s * lam
        if s not in best or best[s] < c:
            best[s] = c
    hull = []
    for s, c in sorted(best.items()):
        while len(hull) >= 2:
            (s1, c1), (s2, c2) = hull[-2], hull[-1]
            if (c1 - c) / (s - s1) <= (c1 - c2) / (s2 - s1):
                hull.pop()
            else:
                break
        hull.append((s, c))
    out = []
    for (s1, c1), (s2, c2) in zip(hull, hull[1:]):
        x = (c1 - c2) / (s2 - s1)
        if lo < x < hi:
            out.append(x)
    return out


def main():
    cdir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE

    # ---- lambda-curve trees -------------------------------------------------
    stats = []
    for p in sorted(cdir.glob("cert_lambda_*.json")):
        st = ck.check_cert(str(p), verbose=False)
        require(st["attained"], f"recorded point of {p.name} is not an exact optimum")
        stats.append(st)
    require(len(stats) >= 2, "need at least two lambda-curve trees")
    stats.sort(key=lambda s: s["lambda"])
    print("grid values D*(lambda) (exact, attained):")
    for s in stats:
        print(f"  lambda={s['lambda']}  D*={s['Dstar']} ({float(s['Dstar']):.6f})  leaves={s['leaves']}  max budget multiplier={s['max_slope']}")
    print("\nendpoint values of the left tree, E_k(lambda_{k+1}), and comparison function g of Corollary 1.3(ii):")
    for s1, s2 in zip(stats, stats[1:]):
        e = envelope(s1["leaf_affine"], s1["lambda"], s2["lambda"])
        print(f"  [{s1['lambda']}, {s2['lambda']}]: D*(left)={s1['Dstar']} < g(left)={g_compare(s1['lambda'])} : {s1['Dstar'] < g_compare(s1['lambda'])};"
              f"  E_left(right)={e} ({float(e):.6f}) < g(right)={g_compare(s2['lambda'])} ({float(g_compare(s2['lambda'])):.6f}) : {e < g_compare(s2['lambda'])}")
    last = stats[-1]
    e1 = envelope(last["leaf_affine"], last["lambda"], F(1))
    print(f"  [{last['lambda']}, 1]: E_{last['lambda']}(1)={e1} ({float(e1):.6f}) (not needed: the (**) tree gives the bound near 1);"
          f" 71/130 + (mu - 9/10) < (23 mu + 3)/40  iff  mu < {(F(39, 40) - F(71, 130)) / F(17, 40)}")

    # ---- (**) tree ------------------------------------------------------------
    cert = cs.load_certificate(cdir / "cert_starstar.json")
    info = cs.verify_certificate(cert)
    la = leaf_affine_starstar(cert["tree"])
    smax = max(s for _, s in la)
    thr = min((F(3, 5) - b) / s for b, s in la if s > 0)
    print(f"\n(**) tree at budget 1: {len(la)} leaves, max leaf bound {info['max_certified_D']}, max budget multiplier {smax} ({float(smax):.6f})")
    print(f"  E_1(mu) <= 3/5  iff  mu <= 1 + {thr} = {1 + thr} ({float(1 + thr):.6f})")
    for mu in (F(1), F(1007, 1000), 1 + thr, F(101, 100), F(21, 20), F(11, 10)):
        print(f"  E_1({mu}) = {envelope(la, F(1), mu)} ({float(envelope(la, F(1), mu)):.6f})")
    print(f"  endpoints for Corollary 1.3(ii) on [1, 1.10]: E_1(1)={info['max_certified_D']} < 13/20 : {F(info['max_certified_D']) < F(13, 20)};"
          f"  E_1(11/10)={envelope(la, F(1), F(11, 10))} < 283/400 : {envelope(la, F(1), F(11, 10)) < F(283, 400)}")

    # ---- the bound beta(mu) -----------------------------------------------------
    def beta(mu):
        if mu <= last["lambda"]:
            left = max((s for s in stats if s["lambda"] <= mu), key=lambda s: s["lambda"])
            right = min((s for s in stats if s["lambda"] >= mu), key=lambda s: s["lambda"])
            return min(envelope(left["leaf_affine"], left["lambda"], mu),
                       envelope(right["leaf_affine"], right["lambda"], mu), right["Dstar"])
        if mu <= 1:
            return min(envelope(last["leaf_affine"], last["lambda"], mu), envelope(la, F(1), mu))
        return envelope(la, F(1), mu)

    print("\nbeta(mu) = min(E_left(mu), E_right(mu), D*(right)) on [0.70, 0.90], min(E_0.90(mu), E_1(mu)) on [0.90, 1], E_1(mu) on [1, 1.10]")
    print("  mu | beta(mu) | exact | (23mu+3)/40 | 2mu/3 | 3/5 (lambda<1) | g(mu)")
    grid = sorted({F(k, 100) for k in range(70, 111)} | {F(k, 1000) for k in range(725, 1100, 50)})
    for mu in grid:
        bound = beta(mu)
        prev = f"{float(F(3, 5)):.4f}" if mu < 1 else "  n/a "
        print(f"  {float(mu):.3f} | {float(bound):.6f} | {bound} | {float((23*mu+3)/40):.4f} | {float(2*mu/3):.4f} | {prev} | {float(g_compare(mu)):.6f}")

    # ---- Corollary 1.3(ii) at every breakpoint ---------------------------------
    lo, hi = F(7, 10), F(11, 10)
    cand = {lo, hi, F(1), F(9, 11), F(9, 10), F(21, 23)}  # endpoints, jump of g, breakpoints of g
    cand.update(s["lambda"] for s in stats)
    for s in stats:
        cand.update(envelope_breakpoints(s["leaf_affine"], s["lambda"], lo, hi))
    cand.update(envelope_breakpoints(la, F(1), lo, hi))
    # crossings between the component functions of beta (where the minimum switches)
    comps = [lambda mu, s=s: envelope(s["leaf_affine"], s["lambda"], mu) for s in stats]
    comps.append(lambda mu: envelope(la, F(1), mu))
    comps += [lambda mu, s=s: s["Dstar"] for s in stats]
    pts = sorted(cand)
    extra = set()
    for x0, x1 in zip(pts, pts[1:]):
        for i in range(len(comps)):
            for j in range(i + 1, len(comps)):
                d0 = comps[i](x0) - comps[j](x0)
                d1 = comps[i](x1) - comps[j](x1)
                if d0 * d1 < 0:
                    extra.add(x0 + (x1 - x0) * d0 / (d0 - d1))
    cand.update(extra)
    pts = sorted(cand)
    gaps = [(g_compare(x) - beta(x), x, "") for x in pts]
    g_left_1 = min(F(13, 20), F(2, 3), F(3, 5))
    gaps.append((g_left_1 - beta(F(1)), F(1), " (left limit mu -> 1-)"))
    require(all(gp > 0 for gp, _, _ in gaps), "beta(mu) >= g(mu) at some breakpoint")
    gmin = min(gaps)
    print(f"\nCorollary 1.3(ii): beta(mu) < g(mu) at all {len(pts)} breakpoints of beta and g in [0.70, 1.10] and at mu -> 1-: True")
    print(f"  smallest gap g - beta = {gmin[0]} ({float(gmin[0]):.6f}) at mu = {gmin[1]}{gmin[2]};  3/5 - 5588/9417 = {F(3, 5) - F(5588, 9417)}")
    print("ALL PARAMETRIC CHECKS PASSED.")


if __name__ == "__main__":
    main()
