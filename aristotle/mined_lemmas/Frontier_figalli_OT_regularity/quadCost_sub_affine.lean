/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem quadCost_sub_affine (y y' : E) :
    ∃ (a : E) (b : ℝ), ∀ x : E, quadCost x y - quadCost x y' = ⟪a, x⟫_ℝ + b := by
  refine ⟨y' - y, (‖y‖ ^ 2 - ‖y'‖ ^ 2) / 2, fun x => ?_⟩
  simp only [quadCost, norm_sub_sq_real, inner_sub_left, real_inner_comm y' x,
    real_inner_comm y x]
  ring

/-- **Subgradient inequality.** If `u` is convex on a convex set `Ω` and differentiable at
`y ∈ Ω`, then its gradient at `y` is a subgradient: `⟪∇u(y), z - y⟫ ≤ u z - u y` for `z ∈ Ω`. -/
