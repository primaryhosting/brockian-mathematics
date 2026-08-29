import Mathlib
/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
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

namespace CS

/-- A comparison-based decision tree sorting 4 elements.

An input is modelled by a permutation `σ : Equiv.Perm (Fin 4)`, where `σ i` is the rank
of the `i`-th input element (so all inputs are distinct and every ranking occurs).
An internal node `node i j l r` performs the single comparison `σ i ≤ σ j`, i.e. it asks
whether the `i`-th element is smaller than the `j`-th element, and branches accordingly.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree

/-- The output of the decision tree on the input with ranking `σ`. -/

theorem sorting_lb_4 (t : DTree) (h : Correct t) :
    ⌈Real.logb 2 (Nat.factorial 4 : ℝ)⌉ ≤ (depth t : ℤ) := by
  have h5 : (5:ℕ) ≤ depth t := five_le_depth t h
  have hceil : ⌈Real.logb 2 (Nat.factorial 4 : ℝ)⌉ ≤ (5 : ℤ) := by
    rw [Int.ceil_le]
    have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h24]
    have hle : Real.logb 2 24 ≤ Real.logb 2 32 := by
      apply Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
    have h32 : Real.logb 2 32 = 5 := by
      rw [show (32:ℝ) = 2 ^ (5:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
    push_cast
    linarith
  exact le_trans hceil (by exact_mod_cast h5)

/-! ### Non-vacuity: correct decision trees do exist -/

/-- A permutation of `Fin 4` is determined by the outcomes of all comparisons. -/
