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

def SatisfiesMTW (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ A : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ,
    (∀ x y, (Matrix.of fun i j => costMixed c i j x y) * A x y = 1) →
      ∀ x y ξ η : Fin n → ℝ, (∑ i, ξ i * η i = 0) → 0 ≤ MTWtensor c A x y ξ η

/-- The quadratic cost `c(x,y) = |x - y|² / 2` in coordinates. -/
