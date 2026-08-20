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

lemma pdy_pdx_quadCost (i k : Fin n) :
    pdy (pdx (quadCost n) i) k = fun _ _ => -(if i = k then (1 : ℝ) else 0) := by
  funext x y
  rw [pdx_quadCost]
  show deriv (fun t : ℝ => x i - Function.update y k t i) (y k) = _
  by_cases hik : i = k
  · subst hik
    have heq : (fun t : ℝ => x i - Function.update y i t i) = fun t : ℝ => x i - t := by
      funext t; rw [Function.update_self]
    rw [heq, if_pos rfl]
    have : HasDerivAt (fun t : ℝ => x i - t) (-1) (y i) := by
      simpa using (hasDerivAt_id (y i)).const_sub (x i)
    simp [this.deriv]
  · have heq : (fun t : ℝ => x i - Function.update y k t i) = fun _ : ℝ => x i - y i := by
      funext t; rw [Function.update_of_ne hik]
    rw [heq, if_neg hik, deriv_const]
    ring

