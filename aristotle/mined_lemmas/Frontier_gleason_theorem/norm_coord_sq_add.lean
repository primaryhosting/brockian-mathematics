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

theorem norm_coord_sq_add (x : C2) (hx : ‖x‖ = 1) :
    ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_eq x
  rw [hx] at h
  rw [show (∑ i, ‖x.ofLp i‖ ^ 2) = ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 by
    simp [Fin.sum_univ_two]] at h
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2), h]

/-- Coordinatewise consequence of orthogonality in `ℂ²`. -/
