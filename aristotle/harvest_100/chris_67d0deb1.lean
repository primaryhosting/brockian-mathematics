/-
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

/-- The spectral gap of the cycle family `C n` vanishes as `n → ∞`:
`2 - 2 cos (2π/n) → 0`.  Hence the plain cycle family has no uniform spectral gap. -/
theorem cycle_gap_vanishes :
    Filter.Tendsto cycleGap Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have h2 := (Real.continuous_cos.tendsto 0).comp h1
  simp only [Real.cos_zero] at h2
  have h3 := h2.const_mul (2 : ℝ)
  have h4 := tendsto_const_nhds.sub h3 (f := fun _ : ℕ => (2 : ℝ))
  simpa [cycleGap] using h4

end Frontier.Spectral

