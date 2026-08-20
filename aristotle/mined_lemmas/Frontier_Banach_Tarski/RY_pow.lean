import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma RY_pow (t : ℝ) (n : ℕ) : RY t ^ n = RY (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, RY_zero]
  | succ m ih =>
      rw [pow_succ, ih, ← RY_add]
      congr 1
      push_cast
      ring

