import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Math

/-- Algebraic identity: the positive root of `‖a + t v‖² = 1` (with `‖a‖ ≤ 1`, `v ≠ 0`)
is `t = (-⟪a,v⟫ + √(⟪a,v⟫² + ‖v‖²(1-‖a‖²)))/‖v‖²`. -/

theorem brouwer_2d_disk
    (f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (hf : Continuous f) :
    ∃ x, f x = x := by
  have hmem : ∀ x : EuclideanSpace ℝ (Fin 2),
      (max 1 ‖x‖)⁻¹ • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro x
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have h1 : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
    have h2 : ‖x‖ ≤ max 1 ‖x‖ := le_max_right _ _
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith), inv_mul_le_iff₀ (by linarith)]
    linarith
  set proj : EuclideanSpace ℝ (Fin 2) → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun x => ⟨(max 1 ‖x‖)⁻¹ • x, hmem x⟩ with hproj
  have hprojc : Continuous proj := by
    apply Continuous.subtype_mk
    refine Continuous.smul ((continuous_const.max continuous_norm).inv₀ ?_) continuous_id
    intro x
    have : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
    linarith
  set g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x => (f (proj x) : EuclideanSpace ℝ (Fin 2))
  have hgc : Continuous g := continuous_subtype_val.comp (hf.comp hprojc)
  obtain ⟨x, hx, hgx⟩ := brouwer_2d g hgc.continuousOn (fun x _ => (f (proj x)).2)
  have hxle : ‖x‖ ≤ 1 := by simpa using hx
  have hpx : proj x = ⟨x, hx⟩ := Subtype.ext (by simp [hproj, max_eq_left hxle])
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  show (f ⟨x, hx⟩ : EuclideanSpace ℝ (Fin 2)) = x
  rw [← hpx]
  exact hgx

end Math

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

