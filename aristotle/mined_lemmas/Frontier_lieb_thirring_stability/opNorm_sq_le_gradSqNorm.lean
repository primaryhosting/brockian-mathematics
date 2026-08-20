/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

lemma opNorm_sq_le_gradSqNorm (ψ : Space → ℂ) (x : Space) :
    ‖fderiv ℝ ψ x‖ ^ 2 ≤ gradSqNorm ψ x := by
  set L : Space →L[ℝ] ℂ := fderiv ℝ ψ x with hL
  set S : ℝ := ∑ j : Fin 3, ‖L (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ‖L‖ ≤ Real.sqrt S := by
    refine L.opNorm_le_bound (Real.sqrt_nonneg _) fun x => ?_
    have hx : x = ∑ j : Fin 3, (x j) • (EuclideanSpace.single j (1 : ℝ)) := by
      ext i; simp [Pi.single_apply]
    have h1 : ‖L x‖ ≤ ∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖ := by
      calc ‖L x‖ = ‖∑ j : Fin 3, (x j) • L (EuclideanSpace.single j (1 : ℝ))‖ := by
            conv_lhs => rw [hx]
            simp [map_sum]
        _ ≤ ∑ j : Fin 3, ‖(x j) • L (EuclideanSpace.single j (1 : ℝ))‖ := norm_sum_le _ _
        _ = _ := by simp
    have hsum0 : 0 ≤ ∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖ :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h2 : (∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        ≤ (∑ j : Fin 3, |x j| ^ 2) * S :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hnx : ‖x‖ = Real.sqrt (∑ j : Fin 3, |x j| ^ 2) := by
      rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs]
    have h3 : (∑ j : Fin 3, |x j| * ‖L (EuclideanSpace.single j (1 : ℝ))‖)
        ≤ Real.sqrt ((∑ j : Fin 3, |x j| ^ 2) * S) := by
      have h4 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq hsum0] at h4
    calc ‖L x‖ ≤ _ := h1
      _ ≤ Real.sqrt ((∑ j : Fin 3, |x j| ^ 2) * S) := h3
      _ = Real.sqrt S * ‖x‖ := by
          rw [hnx, Real.sqrt_mul (by positivity)]; ring
  have hgrad : gradSqNorm ψ x = S := rfl
  rw [hgrad]
  have hsq := Real.sq_sqrt hS0
  nlinarith [norm_nonneg L, Real.sqrt_nonneg S]

/-- The constant in the Sobolev inequality `‖ψ‖_6 ≤ sobolevConst ‖Dψ‖_2` on `ℝ³`. -/
