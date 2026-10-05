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

namespace Frontier
namespace Spectral

/-- The Fiedler value (algebraic connectivity) of the cycle graph `C n`. -/
noncomputable def g (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The angles `2π/n` tend to `0` as `n → ∞`. -/
lemma tendsto_angle_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) := by
  simpa using
    (Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * Real.pi))

/-- The Fiedler value of the cycle family tends to `0`: there is no uniform spectral gap. -/
theorem cycle_gap_vanishes : Filter.Tendsto g Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / n)) Filter.atTop
      (nhds (Real.cos 0)) :=
    (Real.continuous_cos.tendsto 0).comp tendsto_angle_atTop
  rw [Real.cos_zero] at h
  have := (tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop (α := ℕ))).sub
    (h.const_mul (2 : ℝ))
  simpa [g] using this

end Spectral
end Frontier

