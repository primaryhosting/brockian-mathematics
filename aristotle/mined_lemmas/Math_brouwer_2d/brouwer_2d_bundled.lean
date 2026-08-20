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

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- If `u` lies in the closed unit disk of `ℂ` and `u ≠ 1`, then `u.re < 1`. -/

theorem brouwer_2d_bundled
    (f : C(closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
          closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    ∃ x, f x = x := by
  classical
  set F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => if hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then (f ⟨y, hy⟩ : _) else 0
    with hF
  have hFc : ContinuousOn F (closedBall 0 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have hr : (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).restrict F
        = fun y => (f y : EuclideanSpace ℝ (Fin 2)) := by
      funext y
      simp only [hF, Set.restrict_apply, dif_pos y.2, Subtype.coe_eta]
    rw [hr]
    exact continuous_subtype_val.comp f.continuous
  have hFm : Set.MapsTo F (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1) := by
    intro y hy
    simp only [hF, dif_pos hy]
    exact (f ⟨y, hy⟩).2
  obtain ⟨x, hx, hfx⟩ := brouwer_2d hFc hFm
  simp only [hF, dif_pos hx] at hfx
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

end Math

