import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-sorting algorithm on `5` elements, modelled as a (binary) decision tree.
A `leaf p` outputs the permutation `p`; a `node i j l r` compares the keys at positions `i`
and `j` and continues in `l` if `key i ≤ key j`, and in `r` otherwise.  This is the standard
decision-tree model: the algorithm's only access to the input is through comparisons. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of the
decision tree. -/

theorem ceil_logb_factorial_five : (⌈Real.logb 2 (Nat.factorial 5)⌉ : ℤ) = 7 := by
  have hf : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  have h64 : Real.logb 2 64 = 6 := by
    rw [show (64:ℝ) = 2 ^ (6:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
  have h128 : Real.logb 2 128 = 7 := by
    rw [show (128:ℝ) = 2 ^ (7:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
  have h1 : Real.logb 2 64 < Real.logb 2 120 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 120 ≤ Real.logb 2 128 :=
    (Real.logb_le_logb (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hf, Int.ceil_eq_iff]
  constructor <;> push_cast <;> linarith

/-- **Comparison-sorting lower bound for 5 elements.**
Any correct comparison sort of `5` elements needs at least `⌈log₂ (5!)⌉ = 7` comparisons
in the worst case (the worst-case number of comparisons being the depth of its decision
tree). -/
