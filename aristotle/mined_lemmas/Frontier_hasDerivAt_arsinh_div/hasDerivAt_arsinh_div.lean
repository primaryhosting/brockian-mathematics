import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
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


lemma hasDerivAt_arsinh_div (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ)) (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
  have h1 : HasDerivAt (fun t : ℝ => t / Δ) (1 / Δ) x := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).mul_const Δ⁻¹
  have h2 := (Real.hasDerivAt_arsinh (x / Δ)).comp x h1
  have hkey : Δ ^ 2 * (1 + (x / Δ) ^ 2) = x ^ 2 + Δ ^ 2 := by
    field_simp; ring
  have hs : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
    rw [eq_div_iff (ne_of_gt hΔ), ← hkey, Real.sqrt_mul (by positivity), Real.sqrt_sq hΔ.le,
      mul_comm]
  have hpos : 0 < Real.sqrt (x ^ 2 + Δ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  convert h2 using 1
  rw [hs]
  field_simp

