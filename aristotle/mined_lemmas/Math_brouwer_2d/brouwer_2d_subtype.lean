/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set Complex

namespace Math

noncomputable section

/-! ## Step 1: the radial projection onto the closed unit disk of `ℂ`. -/

/-- Radial projection of `ℂ` onto the closed unit disk. -/

theorem brouwer_2d_subtype (f : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
    closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (hf : Continuous f) : ∃ x, f x = x := by
  classical
  set F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun y => if h : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 then
      (f ⟨y, h⟩ : EuclideanSpace ℝ (Fin 2)) else 0 with hF
  have hres : (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).restrict F =
      fun x => (f x : EuclideanSpace ℝ (Fin 2)) := by
    funext x
    simp only [Set.restrict_apply, hF, dif_pos x.2]
  have hFcont : ContinuousOn F (closedBall 0 1) := by
    rw [continuousOn_iff_continuous_restrict, hres]
    exact continuous_subtype_val.comp hf
  have hmapsF : MapsTo F (closedBall 0 1) (closedBall 0 1) := by
    intro y hy
    simp only [hF, dif_pos hy]
    exact (f ⟨y, hy⟩).2
  obtain ⟨x, hx, hfx⟩ := brouwer_2d F hFcont hmapsF
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [hF] at hfx
  simp only [dif_pos hx] at hfx
  exact hfx

end

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

