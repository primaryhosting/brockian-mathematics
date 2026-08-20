import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

set_option grind.warning false

namespace Frontier

/-! ## Partial derivatives of a cost function in coordinates -/

section MTW

variable {n : ℕ}

/-- Partial derivative of a cost `c x y` in the `i`-th coordinate of the source variable `x`. -/

theorem quadCost_mixedHessian_invertible (x y : Fin n → ℝ) :
    (Matrix.of fun i j => costMixed (quadCost n) i j x y) * (-1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [costMixed_quadCost]
  simp

end MTW

/-! ## Base case regularity: Brenier potentials for the quadratic cost -/

section Brenier

open InnerProductSpace

variable {n : ℕ} {ι : Type*}

/-- The quadratic transport cost `c(x,y) = |x - y|²/2` on Euclidean space. -/
