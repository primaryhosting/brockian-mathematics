/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting three elements.
An internal node compares the (unknown) input values at two positions `i j : Fin 3`,
and branches on the outcome; a leaf outputs a permutation. -/
inductive CompTree : Type
  | leaf : Equiv.Perm (Fin 3) → CompTree
  | node : Fin 3 → Fin 3 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem ceil_logb_factorial_three : ⌈Real.logb 2 (Nat.factorial 3)⌉₊ = 3 := by
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6]
  have hub : Real.logb 2 6 ≤ 3 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hlb : (2:ℝ) < Real.logb 2 6 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- **Sorting lower bound for 3 elements.**  Any comparison-based sorting algorithm
for `3` elements — modelled as a decision tree that correctly outputs the ranking of
every one of the `3! = 6` possible inputs — performs at least `⌈log₂ 3!⌉ = 3`
comparisons in the worst case. -/
