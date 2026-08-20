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

noncomputable def costXXYY (c : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (i j k l : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ := pdy (pdy (pdx (pdx c i) j) k) l

/-- The Ma–Trudinger–Wang tensor of a cost `c`, computed with respect to a matrix field `A`
(which is meant to be the inverse of the mixed Hessian `c_{i,j}`):
`S_c(x,y)(ξ,η) = -(3/2) ∑ (c_{ij,r} A^{rs} c_{s,kl} - c_{ij,kl}) ξ^i ξ^j η^k η^l`. -/
