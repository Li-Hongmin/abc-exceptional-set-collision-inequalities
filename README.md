# Collision inequalities and the radical budget for the exceptional set in the abc conjecture

[![Verify certificates](https://github.com/Li-Hongmin/abc-exceptional-set-collision-inequalities/actions/workflows/verify.yml/badge.svg)](https://github.com/Li-Hongmin/abc-exceptional-set-collision-inequalities/actions/workflows/verify.yml)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.24082225-blue)](https://doi.org/10.5281/zenodo.24082225)

**An AI-generated manuscript with computer-checked certificates, released for human verification.**

Hongmin Li (Institute of Science Tokyo; The University of Tokyo) · lihongmin@edu.k.u-tokyo.ac.jp

This repository holds the manuscript in the version accepted on rStation
(problem *math*, paper 17, version 1, 9 November 2026:
<https://rstation.ai/problems/math/papers/17/v1>; archived at Zenodo,
DOI [10.5281/zenodo.24082226](https://doi.org/10.5281/zenodo.24082226)),
the supplement with its exact verifiers and the eleven branch-and-bound
trees, and a continuous-integration workflow that reruns every verifier on a
clean machine using only the Python standard library.

## What is claimed

For $\lambda>0$ let $N_\lambda(X)$ be the number of coprime triples
$a+b=c\le X$ with $\operatorname{rad}(abc)<c^\lambda$. The abc conjecture
predicts $N_\lambda(X)=O_\lambda(1)$ for every fixed $\lambda<1$. Bernert,
Browning, Lichtman and Teräväinen [1] proved $N_\lambda(X)\ll
X^{(23\lambda+3)/40+\varepsilon}$ for $0<\lambda\le2$ and $N_\lambda(X)\ll
X^{3/5+\varepsilon}$ for $0<\lambda<1$; the exponent $3/5$ is the value of
their linear program. The manuscript inserts a generalized collision
inequality into that program and studies how the resulting exponent depends
on the radical budget $\lambda$.

> **Theorem 1.1.** Let $U=54/91=0.593406\ldots$. For every $0<\lambda\le1$
> and every $\varepsilon>0$,
> $$N_\lambda(X)\ll_{\lambda,\varepsilon}X^{U+\varepsilon}.$$
> The proof gives the slightly smaller exponent $5588/9417=0.593394\ldots$
> (Proposition 5.1). Combined with the trivial bound,
> $N_\lambda(X)\ll X^{\min\{2\lambda/3,\,54/91\}+\varepsilon}$; on the common
> domain $0<\lambda<1$ of the bounds of [1], the new exponent improves on both
> $3/5$ and $2\lambda/3$ exactly when $81/91=0.8901\ldots<\lambda<1$. The gain
> over $3/5$ is $3/5-54/91=3/455$, about thirteen times the gain
> $3/5-59969/100033=254/500165$ of [2].

> **Theorem 1.2.** Write $\lambda_0<\lambda_1<\dots<\lambda_4$ for
> $0.70,0.75,0.80,0.85,0.90$.
>
> (a) For $k=0,\dots,4$ let $D^*(\lambda_k)$ be given by
> $$D^*(0.70)=\tfrac{109}{250},\quad D^*(0.75)=\tfrac{35}{76},\quad D^*(0.80)=\tfrac{59}{120},\quad D^*(0.85)=\tfrac{267}{520},\quad D^*(0.90)=\tfrac{71}{130}$$
> (decimal values $0.4360$, $0.4605$, $0.4917$, $0.5135$, $0.5462$). Then
> $N_\lambda(X)\ll_{\lambda,\varepsilon}X^{D^*(\lambda_k)+\varepsilon}$ for
> every $0<\lambda\le\lambda_k$.
>
> (b) There are explicit convex piecewise-linear functions $E_{\lambda_k}$
> ($k=0,\dots,4$) and $E_1$, each the maximum of finitely many affine
> functions of $\mu$ with slopes in $[0,1]$ (respectively $[0,144/143]$ for
> $E_1$), with $E_{\lambda_k}(\lambda_k)=D^*(\lambda_k)$ and
> $E_1(1)=5588/9417$, such that
> $$N_\mu(X)\ll_{\mu,\varepsilon}X^{\beta(\mu)+\varepsilon},\qquad \beta(\mu)=\begin{cases}\min\big(E_{\lambda_k}(\mu),E_{\lambda_{k+1}}(\mu),D^*(\lambda_{k+1})\big),&\mu\in[\lambda_k,\lambda_{k+1}],\ k\le3,\\ \min\big(E_{0.90}(\mu),\,E_1(\mu)\big),&\mu\in[0.90,1],\\ E_1(\mu),&\mu\in[1,1.10].\end{cases}$$
> Since all slopes are non-negative, $E_1(\mu)\le E_1(1)=5588/9417<54/91$ for
> $\mu\le1$. The functions are determined by the trees in the supplement
> (Section 5); a table of values is given in Section 6.
>
> (c) $E_1(\mu)\le3/5$ if and only if $\mu\le247/245=1.00816\ldots$, and
> $E_1(1.05)=89/140=0.6357\ldots$, $E_1(1.10)=6239/9170=0.6803\ldots$.

> **Corollary 1.3.** (i) $N_\lambda(X)\ll_{\lambda,\varepsilon}X^{3/5+\varepsilon}$
> for every $0<\lambda\le247/245$. (ii) For every $\lambda\in[0.70,1.10]$ the
> exponent $\beta(\lambda)$ of Theorem 1.2 is strictly smaller than
> $$g(\lambda)=\begin{cases}\min\{(23\lambda+3)/40,\ 2\lambda/3,\ 3/5\},&\lambda<1,\\ \min\{(23\lambda+3)/40,\ 2\lambda/3\},&\lambda\ge1,\end{cases}$$
> the smallest of the exponents of [1, Theorems 1.2 and 1.3] (the exponent
> $3/5$ being available for $\lambda<1$ only) and of the trivial bound. On
> $[0.70,1)$ the difference $g-\beta$ is at least
> $3/5-5588/9417=311/47085=0.0066\ldots$, and this is its infimum.

Method, in one sentence: after freezing all but a chosen set of powerful
coordinates of two of the three letters, the free monomials satisfy a
congruence modulo the frozen coefficient of the other letter; a Bézout
parametrization of $g^j=h^k$ in the unit group bounds the resulting
multiplicative energy, a uniform count of representations $x^jy^k-x'^jy'^k=m$
bounds the differences, and the inequality so obtained is added to the
linear program of [1], whose value is then bounded by branch-and-bound trees
whose leaves carry rational Farkas multipliers.

The manuscript gives proofs of these statements. They have not been checked
by a human expert.

**Not claimed:**

- not the abc conjecture, nor any bound of the shape $N_\lambda(X)=O(1)$;
- no exponent below $54/91$ at $\lambda=1$: the manuscript shows (Section 7)
  that the constraints it uses cannot give an exponent below $213/359=0.5933\ldots$,
  and it does not show that $5588/9417$ is the value of its own program;
- nothing for $\lambda<0.70$ beyond Theorem 1.1 and the trivial bound,
  and nothing for $\lambda>1.10$;
- the budget-dependent values of Theorem 1.2 are the exact optima of the
  program with the 24 inequalities of [2]; the generalized inequality of
  this paper was run at budget $1$ only;
- no judgement on the correctness of the cited works beyond what the
  manuscript uses from them.

## How this manuscript was produced

The manuscript, the generalized inequality and its proof, the branch-and-bound
trees and the verification programs were produced by AI systems under my
direction. My role was to set goals, allocate compute, and decide when to
stop. **I am not a specialist in analytic number theory, and I cannot
independently vouch for the correctness of the proofs.**

I am releasing it for exactly that reason. If you work on the abc
conjecture, the exceptional set, powerful numbers or the geometry of
numbers, I would be grateful for your reading, whether the outcome is
"correct", "fixable", or "wrong at step X". I will publicly record whichever
it turns out to be.

Substantive verification or correction will be acknowledged. Co-authorship
on any revised version is open to anyone who materially contributes.

## Relation to prior work

The manuscript positions itself as follows; the wording follows its
Sections 1 and 8.

- **Bernert, Browning, Lichtman and Teräväinen, arXiv:2410.12234v2 [1].**
  Supplies the whole framework: the anatomic decomposition into powerful
  parts, the trivial, Fourier and geometry-of-numbers bounds, and the linear
  program whose value is $3/5$. The manuscript uses their Propositions 2.1,
  2.3, 3.1 and 4.1 unchanged and adds one inequality to the program.
  **Where the gains at $\lambda<1$ come from:** the values $D^*(\lambda_k)$
  of Theorem 1.2 are the exact optima of a program whose constraints are
  those of [1] with the budget $\lambda_k$ in place of $1$ and with all
  $2^{18}$ index sets in the geometry-of-numbers bound rather than the
  thirteen used in [1], plus the 24 collision inequalities of [2]. At four
  of the five grid budgets ($0.70,0.75,0.80,0.90$) the same program without
  any collision inequality has the same optimum. So at those budgets the
  whole improvement over [1] comes from running the program of [1] itself at
  budget $\lambda_k$ with all geometric constraints, not from anything new in
  this paper or in [2]. The collision inequalities contribute at
  $\lambda=0.85$ (where the program of [1] alone gives $86/167$) and at
  $\lambda=1$, where the program of [1] has value exactly $3/5$ (a witness
  point is given in Section 8) and the new inequality brings it below
  $54/91$.
- **The author's earlier paper, rStation math 6, version 3 [2]**
  (<https://rstation.ai/problems/math/papers/6/v3>; Zenodo concept DOI
  [10.5281/zenodo.24054868](https://doi.org/10.5281/zenodo.24054868)).
  Introduced the two-letter collision inequality for the exponent pairs
  $(2,3)$ and $(3,4)$ and obtained the exponent $59969/100033$ for
  $0<\lambda\le1$. The present manuscript generalizes that inequality
  (arbitrary coprime exponent pair on one letter, arbitrary nonempty free set
  on the other, one-sided difference bounds for the pairs containing $5$),
  replaces its 777-leaf tree by a 6,078-leaf tree, and adds the dependence
  on the budget, which [2] did not consider. The counting lemma for
  $\mathsf aU^e-\mathsf bV^e=m$ and the framework section are inherited
  from [2] without change; Section 1 of the manuscript lists exactly what is
  inherited and what is new.
- **Bernert, arXiv:2506.13364** and **Runbo Li, arXiv:2507.02885** obtained
  the exponents $0.65$ and $56/85$ before the merged version of [1].
- **Browning and Verzobio, arXiv:2608.24512** treat sums of three powerful
  numbers, a restricted subfamily; their results do not bound the general
  count $N_\lambda(X)$.

To the author's knowledge, no bound below $0.6$ for the general count other
than [2] has appeared, and no bound below $\min\{(23\lambda+3)/40,2\lambda/3\}$
for $\lambda\ge1$. Expert opinion on this positioning is welcome.

## What the computer verification does and does not cover

The continuous-integration workflow (`.github/workflows/verify.yml`) runs
the commands below on every push, on a clean Ubuntu runner with Python 3.12
and nothing installed beyond the standard library. Together they take about
one minute. Before them it extracts the eleven trees from
`supplement/certificates.tar.xz` and checks `supplement/CONTENTS.sha256`,
the checksum manifest of the supplement exactly as submitted, including the
extracted trees. The verifiers raise explicit exceptions rather than using
`assert`, and the workflow reruns two of them under `python -O` to confirm
that no check is lost under optimisation.

| Command (run from `supplement/`) | What it verifies | Manuscript reference |
|---|---|---|
| `python unpack.py` | Extracts the eleven JSON trees (about 11.9 MB) from the solid xz archive. | Section 5, "Reproduction" |
| `sha256sum -c CONTENTS.sha256` | SHA-256 of every supplement file and of the eleven extracted trees. | Data availability |
| `python check_starstar.py` | Rebuilds the 22 root rows, the geometry-of-numbers rows and the nine-branch rows of the generalized inequality from the formulas of Sections 2, 4, 5 and Appendix A, checks node labels and child counts, and checks the Farkas conditions at all 6,078 leaves in exact rational arithmetic, with largest leaf bound $5588/9417<54/91$. Then checks the witness point $D=213/359$ against all $2^{18}$ geometric constraints and all 811,008 instances of the Appendix A inequality, the three symmetric points of Appendix A, and the budget-1 witness $D=3/5$ for the program of [1]. Finally rejects seven deliberately corrupted copies of the tree. | Proposition 5.1; Sections 7 and 8; Appendix A |
| `python check_lambda.py --envelope` | A second verifier, written independently, for the five trees at budgets $0.70,\dots,0.90$ with the 24 inequalities of [2]: Farkas conditions at every leaf, largest leaf bound equal to the declared $D^*(\lambda_k)$, and exact feasibility of the recorded attained point against all constraints. Prints the parametric envelope at the midpoints. | Proposition 5.2; Theorem 1.2(a) |
| `python check_lambda.py cert_base_*.json` | The same for the five trees of the program of [1] without collision inequalities, giving $109/250$, $35/76$, $59/120$, $86/167$, $71/130$. | Section 1, "Where the improvements come from" |
| `python parametric_bounds.py` | Reads the budget multipliers off the verified trees, prints $E_{\lambda_k}$ and $E_1$ and the table of Section 6, reproduces $247/245$, $89/140$, $6239/9170$, and checks $\beta(\mu)<g(\mu)$ in exact arithmetic at every breakpoint in $[0.70,1.10]$ and at the left limit $\mu\to1^-$, reporting the smallest gap $311/47085$. | Lemma 5.3; Theorem 1.2(b),(c); Corollary 1.3 |

**Not reproduced in CI, and not formalized.** This is where a human reader
is needed.

1. Every analytic step: Lemma 3.1 and its reduction table, the counting
   lemma inherited from [2] with its uniform lower bound for fundamental
   units, the Bézout parametrization and energy bound of Lemma 3.2, the
   Cauchy–Schwarz and coprimality steps of Proposition 4.1 and Proposition
   A.1, and the limiting argument of Section 6 that transfers the certified
   inequalities to $N_\lambda(X)$, including the endpoint $\lambda=1$ and the
   range $\lambda>1$.
2. That the rows rebuilt by the verifiers are the inequalities the manuscript
   proves, that is, that the verifier formulas implement Sections 2, 4 and 5
   correctly and are not stronger than what is proved. The two verifiers
   were written independently of the generators and of each other, but both
   were written by AI systems.
3. The cited inputs from [1] (Propositions 2.1, 2.3, 3.1, 4.1 and their
   validity with $L$ in place of $\lambda$ and for $\lambda\le2$).
4. The generation of the trees. The generators `lp_starstar.py` and
   `bb_lambda.py` (which need NumPy and SciPy) are included for
   documentation only; the proofs rest on the stored trees and the
   verifiers, which do not import them.

The checks establish the finite inequalities "every point satisfying these
rows has $D\le\beta$" in exact arithmetic. They do not constitute a proof of
Theorems 1.1 and 1.2.

## Reproducing

Standard library only, Python 3.9 or later, about one minute in total:

```sh
cd supplement
python3 unpack.py
shasum -a 256 -c CONTENTS.sha256      # or: sha256sum -c CONTENTS.sha256
python3 check_starstar.py
python3 check_lambda.py --envelope
python3 check_lambda.py cert_base_0p70.json cert_base_0p75.json cert_base_0p80.json cert_base_0p85.json cert_base_0p90.json
python3 parametric_bounds.py
```

Or fork this repository: the GitHub Actions workflow runs the same commands
on a clean machine.

Regenerating the trees from scratch uses `lp_starstar.py` and
`bb_lambda.py` with NumPy and SciPy; see `supplement/README.txt`. The
regenerated trees need not coincide with the stored ones and must pass the
verifiers on their own.

The PDF was typeset from `paper/paper.md` with pandoc and tectonic; the
title and abstract come from `paper/metadata.json` and the author line was
placed in the YAML header. The Markdown file is the manuscript exactly as
accepted.

## Contents

| Path | What it is |
|---|---|
| `paper/paper.md` | The manuscript as accepted (rStation math 17, version 1) |
| `paper/paper.pdf` | The same manuscript typeset (15 pages) |
| `paper/metadata.json` | Submission title, abstract and tags |
| `supplement/README.txt` | Description of every supplement file and of the checks |
| `supplement/CONTENTS.sha256` | SHA-256 manifest of every supplement file as submitted, including the extracted trees |
| `supplement/certificates.tar.xz` | The eleven branch-and-bound trees (JSON), solid xz archive |
| `supplement/unpack.py` | Extracts the trees next to the verifiers |
| `supplement/check_starstar.py`, `check_lambda.py` | The two independent exact verifiers |
| `supplement/parametric_bounds.py` | Parametric bounds of Section 6 and the breakpoint check of Corollary 1.3(ii) |
| `supplement/lp_starstar.py`, `bb_lambda.py`, `rows_star.py` | Generators of the trees (documentation only; need NumPy and SciPy) |
| `.github/workflows/verify.yml` | CI: extracts the trees, checks the manifest, reruns all verifiers |

## Cite

Hongmin Li, *Collision inequalities and the radical budget for the
exceptional set in the abc conjecture*, rStation, problem math, paper 17,
2026. <https://rstation.ai/problems/math/papers/17>. Archived at Zenodo,
concept DOI [10.5281/zenodo.24082225](https://doi.org/10.5281/zenodo.24082225)
(version 1: [10.5281/zenodo.24082226](https://doi.org/10.5281/zenodo.24082226)).
Source, certificates and verification programs: this repository.

References [1] and [2] above are those of the manuscript:
[1] C. Bernert, T. Browning, J. D. Lichtman, J. Teräväinen, *Bounds on the
exceptional set in the abc conjecture*, arXiv:2410.12234v2;
[2] H. Li, *Breaking the three-fifths barrier for the exceptional set in the
abc conjecture*, rStation math 6, version 3, Zenodo concept DOI
10.5281/zenodo.24054868.

## License

Manuscript and prose: CC BY 4.0. Code and certificate data: MIT. See
`LICENSE`.
