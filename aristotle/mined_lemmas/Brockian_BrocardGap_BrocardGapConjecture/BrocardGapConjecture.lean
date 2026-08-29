import Mathlib

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.BrocardGap

/-! ### Elementary facts about perfect squares -/

/-- If `k` lies strictly between two consecutive squares, it is not a square. -/

theorem BrocardGapConjecture (H : BrocardGapHypothesis) (n m : ℕ) :
    n ! + 1 = m ^ 2 ↔ (n = 4 ∧ m = 5) ∨ (n = 5 ∧ m = 11) ∨ (n = 7 ∧ m = 71) := by
  constructor
  · intro h
    rcases lt_or_ge n 8 with hn | hn
    · interval_cases n
      · exact absurd h (not_sq_of_between (a := 1) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m)
      · exact absurd h (not_sq_of_between (a := 1) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m)
      · exact absurd h (not_sq_of_between (a := 1) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m)
      · exact absurd h (not_sq_of_between (a := 2) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m)
      · exact Or.inl ⟨rfl, eq_of_sq_eq (a := 5) (by rw [← h]; norm_num [Nat.factorial])⟩
      · exact Or.inr (Or.inl ⟨rfl,
          eq_of_sq_eq (a := 11) (by rw [← h]; norm_num [Nat.factorial])⟩)
      · exact absurd h (not_sq_of_between (a := 26) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m)
      · exact Or.inr (Or.inr ⟨rfl,
          eq_of_sq_eq (a := 71) (by rw [← h]; norm_num [Nat.factorial])⟩)
    · rcases le_or_gt 21 n with hn21 | hn21
      · exact absurd h (H n m hn21)
      · exact absurd h (brocardGap_verified_upTo_twenty n m hn (by omega))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [Nat.factorial]

/-! ### A reformulation: Brocard solutions correspond to pronic factorials -/

/-- For `n ≥ 2`, `n ! + 1` is a perfect square if and only if `n !` is four times a
pronic number `a * (a + 1)`. -/
