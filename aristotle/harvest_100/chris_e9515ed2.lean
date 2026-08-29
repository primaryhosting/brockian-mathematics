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
lemma not_sq_of_between {k a : ℕ} (h1 : a ^ 2 < k) (h2 : k < (a + 1) ^ 2) (m : ℕ) :
    k ≠ m ^ 2 := by
  rintro rfl
  have hlt : a < m := by
    by_contra h
    push_neg at h
    nlinarith
  have hgt : m < a + 1 := by
    by_contra h
    push_neg at h
    nlinarith
  omega

/-- Squares determine their (natural number) roots. -/
lemma eq_of_sq_eq {a m : ℕ} (h : a ^ 2 = m ^ 2) : m = a := by
  rcases lt_trichotomy m a with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

/-! ### The Brocard gap hypothesis -/

/-- **Brocard gap hypothesis.**  For every `n ≥ 21` there is a genuine gap between `n ! + 1`
and the perfect squares, i.e. `n ! + 1` is never a perfect square.  This is the open part of
Brocard's problem: the range `8 ≤ n ≤ 20` is settled unconditionally below, so only `n ≥ 21`
needs to be assumed. -/
def BrocardGapHypothesis : Prop := ∀ n m : ℕ, 21 ≤ n → n ! + 1 ≠ m ^ 2

/-- Unconditional verification of the Brocard gap hypothesis in the range `8 ≤ n ≤ 20`:
for each such `n` an explicit integer `a` with `a ^ 2 < n ! + 1 < (a + 1) ^ 2` is exhibited. -/
theorem brocardGap_verified_upTo_twenty (n m : ℕ) (h8 : 8 ≤ n) (h20 : n ≤ 20) :
    n ! + 1 ≠ m ^ 2 := by
  interval_cases n
  · exact not_sq_of_between (a := 200) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 602) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 1904) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 6317) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 21886) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 78911) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 295259) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 1143535) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 4574143) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 18859677) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 80014834) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 348776576) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m
  · exact not_sq_of_between (a := 1559776268) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m

/-! ### The classification of Brocard solutions -/

/-- **Brocard Gap Conjecture (conditional reduction).**
Granting the Brocard gap hypothesis — that `n ! + 1` is not a perfect square for `n ≥ 8` —
the equation `n ! + 1 = m ^ 2` has exactly the three solutions
`(n, m) = (4, 5), (5, 11), (7, 71)`.

The proof splits on the hypothesis `8 ≤ n`: the finitely many cases `n ≤ 7` are settled
unconditionally, and the remaining branch is exactly the assumed gap hypothesis. -/
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
theorem brocard_iff_pronic (n : ℕ) (hn : 2 ≤ n) :
    (∃ m, n ! + 1 = m ^ 2) ↔ ∃ a : ℕ, n ! = 4 * (a * (a + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    have hev : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    have hodd : ¬ 2 ∣ m := by
      rintro ⟨t, rfl⟩
      have h4 : 2 ∣ (2 * t) ^ 2 := ⟨2 * t * t, by ring⟩
      rw [← hm] at h4
      omega
    obtain ⟨a, rfl⟩ : ∃ a, m = 2 * a + 1 := ⟨m / 2, by omega⟩
    refine ⟨a, ?_⟩
    have hx : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
    rw [hx] at hm
    exact Nat.add_right_cancel hm
  · rintro ⟨a, ha⟩
    exact ⟨2 * a + 1, by rw [ha]; ring⟩

end Brockian.BrocardGap

