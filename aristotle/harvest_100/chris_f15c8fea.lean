/-
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier
namespace Spectral

/-- The Fiedler value of the cycle graph `C n`. -/
noncomputable def g (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The argument `2π/n` tends to `0` as `n → ∞`. -/
theorem tendsto_two_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)

/-- The Fiedler value of the cycle family vanishes: `2 - 2 cos(2π/n) → 0`. -/
theorem cycle_gap_vanishes : Filter.Tendsto g Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds 1) := by
    have := (Real.continuous_cos.tendsto 0).comp tendsto_two_pi_div_atTop
    simpa [Function.comp] using this
  have h2 : Filter.Tendsto (fun n : ℕ => 2 - 2 * Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds (2 - 2 * 1)) :=
    (Filter.Tendsto.const_mul (2 : ℝ) h).const_sub 2
  simpa [g] using h2

end Spectral
end Frontier

