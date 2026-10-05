import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *frame function of weight one*, Gleason's formulation of a quantum measure:
a function on the unit sphere which is nonnegative and whose values sum to `1`
over every orthonormal basis. -/
structure IsFrameFunction (f : H → ℝ) : Prop where
  nonneg : ∀ x : H, ‖x‖ = 1 → 0 ≤ f x
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H, ∑ i, f (b i) = 1

/-- A density operator: a positive (hence self-adjoint) operator of trace one. -/

theorem isFrameFunction_qfTwo : IsFrameFunction qfTwo where
  nonneg := by
    intro x _
    unfold qfTwo
    positivity
  sum_eq_one := by
    intro b
    have hrank : Module.finrank ℂ C2 = 2 := by simp
    let e : Fin 2 ≃ Fin (Module.finrank ℂ C2) := finCongr hrank.symm
    rw [(Equiv.sum_comp e (fun i => qfTwo (b i))).symm, Fin.sum_univ_two]
    exact qfTwo_add_qfTwo _ _ (b.norm_eq_one _) (b.norm_eq_one _)
      (b.orthonormal.2 (i := e 0) (j := e 1) (by simp [e, Fin.ext_iff]))

/-- The first standard basis vector of `ℂ²`. -/
