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

lemma costXXYY_quadCost (i j k l : Fin n) :
    costXXYY (quadCost n) i j k l = fun _ _ => (0 : ℝ) := by
  have h : pdy (pdx (pdx (quadCost n) i) j) k = fun _ _ => (0 : ℝ) := costXXY_quadCost i j k
  rw [costXXYY, h]
  exact pdy_of_indep (fun _ => (0 : ℝ)) l

/-- The mixed Hessian of the quadratic cost is `-1`; in particular the cost is nondegenerate. -/
