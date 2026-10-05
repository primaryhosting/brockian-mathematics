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

theorem norm_coord_mul_of_orthogonal (u v : C2) (h : ⟪u, v⟫_ℂ = 0) :
    ‖u.ofLp 0‖ * ‖v.ofLp 0‖ = ‖u.ofLp 1‖ * ‖v.ofLp 1‖ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two] at h
  have h2 : (starRingEnd ℂ) (u.ofLp 0) * v.ofLp 0 = -((starRingEnd ℂ) (u.ofLp 1) * v.ofLp 1) := by
    rw [RCLike.inner_apply, RCLike.inner_apply] at h
    linear_combination h
  simpa [norm_mul] using congrArg norm h2

/-- The real-number identity underlying the two-dimensional counterexample. -/
