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

namespace Brockian.BrocardGap

open Nat

/-- `BrocardFree n` says that `n ! + 1` is not a perfect square, i.e. `n` is not a
solution of Brocard's problem. -/
def BrocardFree (n : ℕ) : Prop := ∀ m : ℕ, n ! + 1 ≠ m ^ 2

/-- `HasGapTwoFactorization n` says that `n !` factors as a product of two natural numbers
whose *gap* is exactly `2`. -/
def HasGapTwoFactorization (n : ℕ) : Prop := ∃ a : ℕ, a * (a + 2) = n !

/-- **Gap reformulation.** `n ! + 1` is a perfect square exactly when `n !` is a product of
two natural numbers differing by `2`. -/
theorem isSquare_factorial_add_one_iff (n : ℕ) :
    (∃ m : ℕ, n ! + 1 = m ^ 2) ↔ HasGapTwoFactorization n := by
  constructor
  · rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hm
      · exact h
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    refine ⟨a, ?_⟩
    have hexp : (a + 1) ^ 2 = a * (a + 2) + 1 := by ring
    omega
  · rintro ⟨a, ha⟩
    exact ⟨a + 1, by rw [← ha]; ring⟩

/-- Contrapositive form of the gap reformulation. -/
theorem brocardFree_iff_not_gapTwo (n : ℕ) :
    BrocardFree n ↔ ¬ HasGapTwoFactorization n := by
  rw [← isSquare_factorial_add_one_iff]
  constructor
  · rintro h ⟨m, hm⟩; exact h m hm
  · intro h m hm; exact h ⟨m, hm⟩

/-- In a gap-two factorization of `n !` with `2 ≤ n` both factors are even. -/
theorem even_of_gapTwo {n a : ℕ} (hn : 2 ≤ n) (ha : a * (a + 2) = n !) : Even a := by
  rcases Nat.even_or_odd a with h | h
  · exact h
  · exfalso
    have hodd : Odd (a * (a + 2)) := h.mul (by simpa using h.add_even (by decide))
    rw [ha] at hodd
    have hdvd : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
    rw [Nat.odd_iff] at hodd
    omega

/-- A modular certificate: if `n ! + 1` is not a quadratic residue mod `q`, then `n` is
Brocard-free. -/
theorem brocardFree_of_mod (n q r : ℕ) (hq : 0 < q) (hr : (n ! + 1) % q = r)
    (h : ((List.range q).all fun x => decide (x * x % q ≠ r)) = true) : BrocardFree n := by
  intro m hm
  have hmem : m % q ∈ List.range q := List.mem_range.mpr (Nat.mod_lt _ hq)
  have hx : (m % q) * (m % q) % q ≠ r := by
    have := List.all_eq_true.mp h (m % q) hmem
    simpa using this
  apply hx
  have hsq : m ^ 2 % q = (m % q) * (m % q) % q := by
    rw [pow_two, Nat.mul_mod]
  rw [← hsq, ← hm, hr]

set_option maxRecDepth 40000

/-- Apart from `n = 4, 5, 7`, no `n < 8` solves Brocard's problem. -/
theorem brocardFree_of_lt_eight (n : ℕ) (hn : n < 8) (h4 : n ≠ 4) (h5 : n ≠ 5) (h7 : n ≠ 7) :
    BrocardFree n := by
  interval_cases n
  · exact brocardFree_of_mod 0 3 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 1 3 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 2 5 3 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 3 5 2 (by norm_num) (by rfl) (by decide)
  · exact absurd rfl h4
  · exact absurd rfl h5
  · exact brocardFree_of_mod 6 11 6 (by norm_num) (by rfl) (by decide)
  · exact absurd rfl h7

/-- The three known solutions of Brocard's problem. -/
theorem not_brocardFree_four_five_seven :
    ¬ BrocardFree 4 ∧ ¬ BrocardFree 5 ∧ ¬ BrocardFree 7 := by
  refine ⟨fun h => h 5 ?_, fun h => h 11 ?_, fun h => h 71 ?_⟩ <;> rfl

/-- **Partial verification.** No `n` with `8 ≤ n ≤ 100` solves Brocard's problem. -/
theorem brocardFree_of_mem_Icc (n : ℕ) (h1 : 8 ≤ n) (h2 : n ≤ 100) : BrocardFree n := by
  interval_cases n
  · exact brocardFree_of_mod 8 11 6 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 9 11 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 10 13 7 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 11 13 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 12 29 17 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 13 23 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 14 31 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 15 37 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 16 19 10 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 17 19 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 18 31 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 19 23 5 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 20 29 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 21 31 6 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 22 37 31 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 23 59 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 24 31 23 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 25 31 24 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 26 29 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 27 29 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 28 43 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 29 37 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 30 37 14 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 31 41 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 32 41 13 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 33 37 32 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 34 37 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 35 37 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 36 41 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 37 43 20 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 38 53 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 39 43 37 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 40 43 22 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 41 43 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 42 47 46 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 43 61 44 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 44 53 50 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 45 53 33 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 46 71 68 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 47 53 20 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 48 53 12 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 49 67 50 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 50 53 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 51 53 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 52 59 55 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 53 59 31 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 54 67 50 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 55 59 11 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 56 59 30 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 57 59 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 58 61 31 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 59 61 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 60 67 5 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 61 67 44 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 62 89 38 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 63 67 57 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 64 67 34 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 65 67 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 66 71 69 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 67 71 13 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 68 79 63 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 69 73 62 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 70 83 14 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 71 79 75 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 72 83 57 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 73 79 28 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 74 79 24 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 75 83 19 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 76 97 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 77 89 28 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 78 83 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 79 83 15 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 80 83 42 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 81 83 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 82 89 12 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 83 89 24 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 84 97 41 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 85 103 27 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 86 101 51 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 87 101 8 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 88 101 11 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 89 101 83 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 90 101 8 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 91 97 39 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 92 97 5 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 93 97 82 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 94 101 32 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 95 103 45 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 96 107 54 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 97 101 18 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 98 101 51 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 99 101 2 (by norm_num) (by rfl) (by decide)
  · exact brocardFree_of_mod 100 139 132 (by norm_num) (by rfl) (by decide)

/-- **Brocard Gap Conjecture** (Lean-checked reduction and partial verification).

The full conjecture — that `n ! + 1` is never a perfect square for `n ≥ 8` — is open.
What is proved here is:

* the *gap* reformulation: `n ! + 1` is a square iff `n !` is a product of two naturals
  with gap exactly `2`;
* the exact determination of the solutions below `8`, namely `4, 5, 7`;
* the verification that no `n` in the range `8 ≤ n ≤ 100` is a solution;
* the resulting equivalence of the conjecture with its gap-free reformulation:
  `n !` has no gap-two factorization for every `n ≥ 8`.
-/
theorem BrocardGapConjecture :
    (∀ n : ℕ, BrocardFree n ↔ ¬ HasGapTwoFactorization n) ∧
    (∀ n : ℕ, n < 8 → (¬ BrocardFree n ↔ (n = 4 ∨ n = 5 ∨ n = 7))) ∧
    (∀ n : ℕ, 8 ≤ n → n ≤ 100 → BrocardFree n) ∧
    ((∀ n : ℕ, 8 ≤ n → BrocardFree n) ↔ (∀ n : ℕ, 8 ≤ n → ¬ HasGapTwoFactorization n)) := by
  obtain ⟨h4, h5, h7⟩ := not_brocardFree_four_five_seven
  refine ⟨brocardFree_iff_not_gapTwo, ?_, brocardFree_of_mem_Icc, ?_⟩
  · intro n hn
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      exact h (brocardFree_of_lt_eight n hn hc.1 hc.2.1 hc.2.2)
    · rintro (rfl | rfl | rfl)
      · exact h4
      · exact h5
      · exact h7
  · constructor
    · intro h n hn
      exact (brocardFree_iff_not_gapTwo n).mp (h n hn)
    · intro h n hn
      exact (brocardFree_iff_not_gapTwo n).mpr (h n hn)

end Brockian.BrocardGap

