import Mathlib

/-!
# Cycle Gap Vanishes
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier.Spectral

/-- The Fiedler value of the cycle graph `C n`. -/

theorem tendsto_two_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) := by
  simpa using
    (Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * Real.pi))

/-- The Fiedler value of the cycle `C n` tends to `0`, so the plain cycle family
has no uniform spectral gap. -/
