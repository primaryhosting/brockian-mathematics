/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `5` elements.
A `node i j l r` compares the elements at positions `i` and `j`, continuing in `l`
if the `i`-th one is smaller and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem ceil_logb_two_factorial_five : ⌈Real.logb 2 (Nat.factorial 5)⌉ = 7 := by
  have hfac : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hfac]
  have h1 : Real.logb 2 120 ≤ 7 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num),
      show ((7 : ℝ)) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2 : (6 : ℝ) < Real.logb 2 120 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num),
      show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hle : ⌈Real.logb 2 120⌉ ≤ 7 :=
    Int.ceil_le.2 (by exact_mod_cast h1 : Real.logb 2 120 ≤ ((7 : ℤ) : ℝ))
  have hlt : (6 : ℤ) < ⌈Real.logb 2 120⌉ :=
    Int.lt_ceil.2 (by exact_mod_cast h2 : ((6 : ℤ) : ℝ) < Real.logb 2 120)
  omega

/-- **Comparison-sorting lower bound for 5 elements, real-logarithm form.**
Any correct comparison-based sorting decision tree for `5` elements makes at least
`⌈log₂(5!)⌉` comparisons in the worst case. -/
