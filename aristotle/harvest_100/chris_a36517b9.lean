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
noncomputable def cycleGap (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The argument `2π/n` tends to `0` as `n → ∞`. -/
theorem tendsto_two_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) := by
  simpa using
    (Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * Real.pi))

/-- The Fiedler value of the cycle `C n` tends to `0`, so the plain cycle family
has no uniform spectral gap. -/
theorem cycle_gap_vanishes :
    Filter.Tendsto (fun n : ℕ => 2 - 2 * Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds 1) := by
    have := (Real.continuous_cos.tendsto 0).comp tendsto_two_pi_div_atTop
    simpa [Function.comp] using this
  have := (tendsto_const_nhds (x := (2 : ℝ)) (f := (Filter.atTop : Filter ℕ))).sub
    (h.const_mul (2 : ℝ))
  simpa using this

/-- Restatement in terms of `cycleGap`. -/
theorem tendsto_cycleGap_atTop_nhds_zero :
    Filter.Tendsto cycleGap Filter.atTop (nhds 0) :=
  cycle_gap_vanishes

end Frontier.Spectral

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

