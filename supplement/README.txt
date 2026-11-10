Supplement to "Collision inequalities and the radical budget for the exceptional set in the abc conjecture"

Contents
  README.txt              this file
  CONTENTS.sha256         SHA-256 of every file below and of the eleven JSON files inside the archive
  certificates.tar.xz     solid xz archive of the eleven branch-and-bound trees (JSON); see "Unpacking"
  unpack.py               extracts the archive into this directory (standard library)
  check_starstar.py       verifier for cert_starstar.json (Proposition 5.1) and the feasible points of
                          Sections 7 and 8 and Appendix A; standard library only (fractions.Fraction);
                          imports no other file
  check_lambda.py         verifier for the budget trees (Proposition 5.2) and their attained points, with the
                          parametric envelope of Lemma 5.3; standard library only; imports no other file
  parametric_bounds.py    prints the values of E_lambda, E_1 and beta(mu) quoted in Section 6 and checks
                          beta(mu) < g(mu) of Corollary 1.3(ii) at every breakpoint in [0.70, 1.10] (imports the
                          two verifiers above; standard library only)
  lp_starstar.py          generator of cert_starstar.json (branch-and-bound with floating-point LP to propose
                          bases, every multiplier re-derived in Fraction before writing); needs numpy, scipy
  bb_lambda.py            generator of cert_lambda_*.json and cert_base_*.json; needs numpy, scipy, and
                          rows_star.py in the same directory
  rows_star.py            row formulas of the program with the 24 inequalities (*), imported by bb_lambda.py
                          only; standard library only

Trees inside certificates.tar.xz (uncompressed sizes in bytes)
  cert_starstar.json      2,303,278   budget 1, family (**): 6,078 leaves, 1,349 (B4) nodes, 591 (**) nodes,
                                      every leaf bound <= 5588/9417 < 54/91
  cert_lambda_0p70.json     337,983   budget 0.70, family (*): D* = 109/250, 713 leaves, attained
  cert_lambda_0p75.json     144,738   budget 0.75: D* = 35/76, 314 leaves, attained
  cert_lambda_0p80.json   2,649,071   budget 0.80: D* = 59/120, 5,286 leaves, attained
  cert_lambda_0p85.json   1,080,788   budget 0.85: D* = 267/520, 2,313 leaves, attained
  cert_lambda_0p90.json   3,125,742   budget 0.90: D* = 71/130, 6,667 leaves, attained
  cert_base_0p70.json       330,586   budget 0.70, program without (*): 109/250, 694 leaves, attained
  cert_base_0p75.json       142,219   budget 0.75, without (*): 35/76, 304 leaves, attained
  cert_base_0p80.json     1,060,240   budget 0.80, without (*): 59/120, 2,093 leaves, attained
  cert_base_0p85.json       521,446   budget 0.85, without (*): 86/167, 1,060 leaves, attained
  cert_base_0p90.json       179,461   budget 0.90, without (*): 71/130, 377 leaves, attained

Unpacking
  The trees total about 11.9 MB uncompressed, above the size limit of the submission platform, so they are
  shipped as one solid xz archive (about 1.8 MB).  Either of
      python3 unpack.py
      tar -xJf certificates.tar.xz
  writes the eleven JSON files into this directory (the verifiers look for them there).  Then
      shasum -a 256 -c CONTENTS.sha256        (or: sha256sum -c CONTENTS.sha256)
  checks every file including the extracted ones.  Before unpacking, the eleven JSON lines of
  CONTENTS.sha256 report "missing"/"FAILED open or read"; this is expected.

Reproduce (Python >= 3.9; the verifiers need nothing outside the standard library)
  python3 unpack.py
  python3 check_starstar.py                 # Proposition 5.1 tree; points of Sections 7, 8, Appendix A; about 20 s
  python3 check_lambda.py --envelope        # Proposition 5.2 trees (cert_lambda_*.json), attained points,
                                            # midpoint envelope; about 20 s
  python3 check_lambda.py cert_base_0p70.json cert_base_0p75.json cert_base_0p80.json cert_base_0p85.json cert_base_0p90.json
                                            # trees for the program without (*); about 10 s
  python3 parametric_bounds.py              # values of E_lambda, E_1 and beta(mu) of Section 6, breakpoint check
                                            # of Corollary 1.3(ii); about 60 s

  check_starstar.py also re-runs itself on seven deliberately corrupted copies of the tree and reports that
  each is rejected; these lines are expected output, not failures.

What is verified
  check_starstar.py rebuilds the 22 root rows, the (B4) rows and the nine-branch (**) rows from the formulas of
  Sections 2, 4, 5 and Appendix A (no code shared with lp_starstar.py), checks node labels (coprime exponent
  pair, k_B in I_B, subsets of {1,...,6}), the number of children (2 or 9), and at each leaf the Farkas conditions
  (y^T A)_D = 1, (y^T A)_v >= 0, y^T b = declared bound <= 5588/9417 < 54/91 in exact rational arithmetic.  It then
  checks the point D = 213/359 of Section 7 against the root rows, all 2^18 constraints (B4), the Thue and
  determinant constraints of the first arXiv version of the reference paper, and all 811,008 instances of the
  inequality of Appendix A (which contain the 4,158 instances of (**) as the case O_C empty); the three symmetric
  points of Appendix A (D = 16/27, 16/27, 7/12), each against the root rows, all 2^18 constraints (B4) and its
  family ((*), (**) with O_C empty, the full family of Appendix A); and the budget-1 witness of Section 8
  (a = b = (0,1,1,0,1,0)/10, c = (0,2,2,0,0,0)/10, D = 3/5) against the root rows and all 2^18 constraints (B4),
  confirming that the program of the reference paper has value exactly 3/5 at budget 1 and that (*) and (**)
  cut this point to 11/20.
  check_lambda.py does the same for the five-branch (*) rows with the budget row a+b+c <= lambda, checks that the
  largest leaf bound equals the declared D*, and checks the recorded point (non-negative coordinates) against the
  root rows, all 24 constraints (*) and all 2^18 constraints (B4) with D = D*.  With --envelope it prints
  E_lambda(mu) = max over leaves of (bound + y_0 (mu - lambda)) at the midpoints between consecutive budgets.

  All checks in the verifiers and in parametric_bounds.py raise explicit exceptions (no assert statements), so
  running them with  python3 -O  does not disable any check; a tampered certificate is rejected either way.

Not included
  Trees of the (*) program at budgets 0.95, 1.00, 1.05, 1.10 and of the program without (*) at budget 1.00 were
  also computed; they exceed the size limit of the platform even compressed and are not part of the claims of the
  paper.  The generators reproduce them (python3 bb_lambda.py 0.95 1.00 1.05 1.10).
