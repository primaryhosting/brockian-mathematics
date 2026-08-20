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

/-- A continuous real function whose cosine is everywhere positive cannot decrease by `2π`
over an interval: the "winding" obstruction. -/

theorem brouwer_2d_euclidean {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hcont : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  have hmem : ∀ z : ℂ,
      z ∈ closedBall (0:ℂ) 1 ↔ e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z
    simp [e.norm_map]
  have hcont' : ContinuousOn (fun w : ℂ => e.symm (f (e w))) (closedBall 0 1) :=
    e.symm.continuous.comp_continuousOn
      (hcont.comp e.continuous.continuousOn fun w hw => (hmem w).1 hw)
  have hmaps' : MapsTo (fun w : ℂ => e.symm (f (e w))) (closedBall (0:ℂ) 1) (closedBall 0 1) := by
    intro w hw
    have h2 := hmaps ((hmem w).1 hw)
    simpa [mem_closedBall_zero_iff, e.symm.norm_map] using h2
  obtain ⟨z, hz, hfz⟩ := brouwer_2d hcont' hmaps'
  refine ⟨e z, (hmem z).1 hz, ?_⟩
  have := congrArg e hfz
  simpa using this

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

