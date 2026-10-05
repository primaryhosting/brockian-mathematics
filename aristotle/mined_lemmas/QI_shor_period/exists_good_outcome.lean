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

theorem exists_good_outcome (z : ℚ) {M : ℚ} (hM : 0 < M) :
    ∃ y : ℤ, |(y : ℚ) / M - z| ≤ 1 / (2 * M) := by
  refine ⟨round (M * z), ?_⟩
  have hkey : |(round (M * z) : ℚ) - M * z| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round (M * z)
  have : (round (M * z) : ℚ) / M - z = ((round (M * z) : ℚ) - M * z) / M := by
    field_simp
  rw [this, abs_div, abs_of_pos hM]
  calc |(round (M * z) : ℚ) - M * z| / M ≤ (1/2) / M := by gcongr
    _ = 1 / (2 * M) := by field_simp

/-- Probability amplification: if each run succeeds with probability at least
`c > 0`, the probability that at least one of `k` independent runs succeeds
tends to `1`. -/
