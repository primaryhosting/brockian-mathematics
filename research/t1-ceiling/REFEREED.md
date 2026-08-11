# REFEREE VERDICTS — read before trusting RESULTS.txt

**Referee A (failure mode: LP artifacts), 2026-08-11 — own recomputation throughout:**

- **R1 ("band-only LP ceiling = exactly 0.6725007; the paper's constant is the exact ceiling of its unconditional data regime"): REFUTED.**
  1. Conflation: 0.6725007 is the CERTIFICATE-CLASS optimum (CCLM17 Cor. 14, class A₀-restricted), not the DATA-REGIME configuration ceiling — the paper's Remark 1.1 puts that at 0.68185 and Theorem D's optimality is explicitly class-scoped.
  2. Missing-constraint attack succeeded: T1's adversary configurations grossly violate out-of-band spectral positivity S(α) ≥ 0 (down to −198, growing with refinement) — a cost-free admissibility constraint genuine configurations satisfy. Adding it moves the LP 0.6725 → 0.684+. The 0.6725 LP point is an artifact of the relaxation level.
  3. "Exactly" was never measured: referee's refinement-coupled extrapolation limits ≈ 0.6738 (1.3e-3 above), tol behavior falsifies T1's correction model (tol→0 LP is INFEASIBLE), and no dual certificate exists anywhere in the program.
  4. Reproducibility failures: shipped lp_primal3.py A collapses to ψ₁=0 at default na (band-grid aliasing); control_dh.py ships stale parameters failing its own positivity check (the RESULTS-described 3-Fejér/eps=0.002 version DOES work); the fine/veryfine series is not reproducible from shipped scripts; RESULTS silently omits the A*/B* full-species collapses (0.2726/0.3406).

- **R2 ("doubly-positive value 0.682 ± 0.002 brackets and identifies 0.68185"): WEAKENED-TO** — "an on-line doubly-positive 2-level relaxation has value ≈0.682–0.685 at accessible discretizations, rising under refinement, numerically CONSISTENT with 0.68185 at the 2–3e-3 level; no stable limit, no two-sided bracket, no identification (the paper never exhibits the extremal-law object)." Both of T1's estimators were downward-biased; the referee's finer (80,160) intercept (0.68004) falls below T1's claimed bracket floor.

- **Confirmed en passant:** the deep-pair witness mechanism on the certificate side — corrected 3-Fejér kernel: min R = +1.06e-8 on its range, R(2i) = −1.629e5 — negative-out-of-band kernels are killed unconditionally. (Scope questions for this obstruction are Referee B's remit: R3/R4 verdicts pending.)

**Standing instruction:** RESULTS.txt claims R1/R2 are superseded by this file. Nothing from this directory advances to any write-up or site surface except through these verdicts.
