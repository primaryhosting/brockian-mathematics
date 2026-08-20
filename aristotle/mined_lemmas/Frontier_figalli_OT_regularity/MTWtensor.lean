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

noncomputable def MTWtensor (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (A : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x y ξ η : Fin n → ℝ) : ℝ :=
  -(3 / 2) * ∑ i, ∑ j, ∑ k, ∑ l,
    ((∑ r, ∑ s, costXXY c i j r x y * A x y r s * costXYY c s k l x y)
      - costXXYY c i j k l x y) * ξ i * ξ j * η k * η l

/-- The Ma–Trudinger–Wang condition `MTW(0)`: for every inverse `A` of the mixed Hessian of `c`,
the MTW tensor is nonnegative on orthogonal pairs of vectors. -/
