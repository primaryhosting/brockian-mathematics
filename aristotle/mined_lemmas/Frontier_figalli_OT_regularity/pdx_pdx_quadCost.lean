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

lemma pdx_pdx_quadCost (i j : Fin n) :
    pdx (pdx (quadCost n) i) j = fun _ _ => (if i = j then (1 : ℝ) else 0) := by
  funext x y
  rw [pdx_quadCost]
  show deriv (fun t : ℝ => Function.update x j t i - y i) (x j) = _
  by_cases hij : i = j
  · subst hij
    have : HasDerivAt (fun t : ℝ => Function.update x i t i - y i) 1 (x i) := by
      have h1 : HasDerivAt (fun t : ℝ => t - y i) 1 (x i) := (hasDerivAt_id (x i)).sub_const _
      have heq : (fun t : ℝ => Function.update x i t i - y i) = fun t : ℝ => t - y i := by
        funext t; rw [Function.update_self]
      rwa [heq]
    rw [this.deriv, if_pos rfl]
  · have heq : (fun t : ℝ => Function.update x j t i - y i) = fun _ : ℝ => x i - y i := by
      funext t; rw [Function.update_of_ne hij]
    rw [heq, if_neg hij, deriv_const]

