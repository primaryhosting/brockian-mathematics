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

lemma pdx_quadCost (i : Fin n) : pdx (quadCost n) i = fun x y => x i - y i := by
  funext x y
  have h : ∀ k : Fin n, HasDerivAt (fun t : ℝ => (Function.update x i t k - y k) ^ 2)
      (if k = i then 2 * (x i - y i) else 0) (x i) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have : HasDerivAt (fun t : ℝ => (t - y k) ^ 2) (2 * (x k - y k)) (x k) := by
        have h1 : HasDerivAt (fun t : ℝ => t - y k) 1 (x k) :=
          (hasDerivAt_id (x k)).sub_const _
        have := h1.pow 2
        simpa [mul_comm] using this
      simpa [Function.update_self] using this
    · have : (fun t : ℝ => (Function.update x i t k - y k) ^ 2)
          = fun _ : ℝ => (x k - y k) ^ 2 := by
        funext t; rw [Function.update_of_ne hk]
      rw [this, if_neg hk]
      exact hasDerivAt_const _ _
  have hsum : HasDerivAt (fun t : ℝ => ∑ k, (Function.update x i t k - y k) ^ 2)
      (∑ k, if k = i then 2 * (x i - y i) else 0) (x i) := HasDerivAt.fun_sum fun k _ => h k
  have hfin : HasDerivAt (fun t : ℝ => (∑ k, (Function.update x i t k - y k) ^ 2) / 2)
      (x i - y i) (x i) := by
    have := hsum.div_const 2
    simpa [Finset.sum_ite_eq' Finset.univ i (fun _ => 2 * (x i - y i))] using this
  show deriv (fun t : ℝ => quadCost n (Function.update x i t) y) (x i) = x i - y i
  exact hfin.deriv

