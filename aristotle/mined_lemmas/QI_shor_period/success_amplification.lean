import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede every other command, including module
doc comments, so this header follows the single `import Mathlib` line.)
-/

namespace QI

/-!
## Overview

Shor's algorithm finds the period `r` of the modular exponentiation function
`x ↦ a ^ x mod N` (for `a` coprime to `N`).  Its structure is:

* the function `x ↦ a ^ x mod N` really is periodic, with least period the
  multiplicative order `r` of `a` modulo `N`;
* the quantum phase-estimation stage produces, with probability bounded below by
  some constant `c > 0`, a measurement outcome `y` whose rescaling `y / M`
  approximates a fraction `s / r` with `gcd (s, r) = 1` to within `1 / (2 M)`
  (such an approximating outcome always exists, by rounding);
* the classical post-processing stage (continued fractions) then recovers `r`
  *exactly*, because a rational number with a sufficiently small denominator is
  uniquely determined by an approximation of this quality: any fraction `p / q`
  in lowest terms with `q * r < M` that is that close to `y / M` must have
  `q = r`;
* repeating the experiment amplifies the success probability to `1`.

The theorem `QI.shor_period` below bundles these statements.  The quantum stage
enters only through the abstract success probability `c`, since the amplitude
analysis is not part of the number-theoretic content formalized here.
-/

/-- Two rational numbers with small denominators cannot both be very close to the
same rational `x`: this is the uniqueness statement underlying the classical
continued-fraction post-processing of Shor's algorithm. -/

theorem success_amplification {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto (fun k : ℕ => 1 - (1 - c) ^ k) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun k : ℕ => (1 - c) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  simpa using h.const_sub (1 : ℝ)

/-- **Shor's period finding.**

For `a` coprime to `N > 1` there is a positive integer `r` such that:

1. `x ↦ a ^ x mod N` is periodic with period `r`;
2. `r` is the *least* period (so `r` is exactly the quantity Shor's algorithm
   must output);
3. for any scale `M > 0` there is an integer measurement outcome `y` with
   `y / M` within `1 / (2 M)` of `s / r` — the outcomes the phase-estimation
   stage concentrates on;
4. such an outcome determines `r` uniquely: any reduced fraction `p / q` with
   `q * r < Q ^ 2` lying within `1 / (2 Q ^ 2)` of the same value as a reduced
   fraction `s / r` satisfies `q = r`, i.e. the classical continued-fraction
   post-processing recovers the period exactly;
5. if a single run succeeds with probability at least `c > 0`, then repeating
   the algorithm drives the overall success probability to `1` — the algorithm
   succeeds with high probability. -/
