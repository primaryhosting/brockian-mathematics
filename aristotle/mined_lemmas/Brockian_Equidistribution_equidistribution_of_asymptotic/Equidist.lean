import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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

set_option grind.warning false

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

def Equidist (x : ℕ → ℝ) : Submodule ℂ C(𝕋, ℂ) where
  carrier := {f | Tendsto (cavg x f) atTop (𝓝 (∫ z, f z))}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at *
    have h1 : (∫ z, (f + g) z) = (∫ z, f z) + ∫ z, g z := by
      simp only [ContinuousMap.coe_add, Pi.add_apply]
      exact integral_add (integrable_cm f) (integrable_cm g)
    rw [h1]
    refine (hf.add hg).congr (fun N => ?_)
    simp [cavg, Finset.sum_add_distrib, mul_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have h : cavg x ⇑(0 : C(𝕋, ℂ)) = fun _ => (0 : ℂ) := by funext N; simp [cavg]
    rw [h]
    simp
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    have h1 : (∫ z, (c • f) z) = c * ∫ z, f z := by
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [MeasureTheory.integral_const_mul]
    rw [h1]
    refine (hf.const_mul c).congr (fun N => ?_)
    rw [ContinuousMap.coe_smul, cavg_smul]

