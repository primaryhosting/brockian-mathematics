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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace Frontier.Spectral

/-- The Fiedler value (algebraic connectivity) of the cycle graph `C n`. -/
noncomputable def cycleGap (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The spectral gap of the cycle family vanishes as `n → ∞`:
there is no uniform spectral gap for the plain cycle family. -/
theorem cycle_gap_vanishes :
    Filter.Tendsto cycleGap Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa using
      Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * Real.pi)
  have h2 := (Real.continuous_cos.tendsto 0).comp h1
  simp only [Real.cos_zero] at h2
  simpa [cycleGap] using Filter.Tendsto.const_sub (2 : ℝ) (h2.const_mul (2 : ℝ))

end Frontier.Spectral

