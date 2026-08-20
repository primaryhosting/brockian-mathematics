/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Metric Complex

namespace Math

noncomputable section

/-- If `x` lies on the unit circle, `w` lies in the closed unit disk and `w ≠ x`, then the
vector `x - w` makes an acute angle with `x`. -/

theorem brouwer_2d_euclideanSpace (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : Set.MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f z = z := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  have hmem : ∀ z : ℂ, e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      z ∈ closedBall (0 : ℂ) 1 := by
    intro z
    simp
  have hgc : ContinuousOn (fun z : ℂ => e.symm (f (e z))) (closedBall 0 1) := by
    apply e.symm.continuous.comp_continuousOn
    apply hf.comp e.continuous.continuousOn
    intro z hz
    exact (hmem z).2 hz
  have hgm : Set.MapsTo (fun z : ℂ => e.symm (f (e z))) (closedBall 0 1) (closedBall 0 1) := by
    intro z hz
    have h : f (e z) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := hmaps ((hmem z).2 hz)
    simpa using h
  obtain ⟨z, hz, hfz⟩ := brouwer_2d _ hgc hgm
  refine ⟨e z, (hmem z).2 hz, ?_⟩
  have := congrArg e hfz
  simpa using this

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

