/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


theorem exists_determining_set (s : BV n) (hs : s ≠ 0) :
    ∃ Y : Finset (BV n), Y.card ≤ n ∧ (∀ y ∈ Y, dotp s y = 0) ∧
      ∀ t : BV n, (∀ y ∈ Y, dotp t y = 0) → t = 0 ∨ t = s := by
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hs (funext hc)
  have hi1 : s i = 1 := (zmod2_cases (s i)).resolve_left hi
  set yv : Fin n → BV n :=
    fun j k => (if k = j then 1 else 0) + (if k = i then s j else 0) with hyv
  have hdot : ∀ (t : BV n) (j : Fin n), dotp t (yv j) = t j + t i * s j := by
    intro t j
    simp [dotp, hyv, mul_add, Finset.sum_add_distrib, mul_ite,
      Finset.sum_ite_eq' Finset.univ j t]
  refine ⟨(Finset.univ.erase i).image yv, ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_image_le.trans Finset.card_erase_le) (by simp)
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    rw [hdot, hi1]
    generalize s j = a
    revert a
    decide
  · intro t ht
    have key : ∀ j, j ≠ i → t j = t i * s j := by
      intro j hj
      have hj0 :=
        ht (yv j) (Finset.mem_image_of_mem yv (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩))
      rw [hdot] at hj0
      have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h2 _ _ hj0
    rcases zmod2_cases (t i) with h0 | h1
    · left
      funext k
      by_cases hk : k = i
      · subst hk; simpa using h0
      · simpa [h0] using key k hk
    · right
      funext k
      by_cases hk : k = i
      · subst hk; rw [h1, hi1]
      · simpa [h1] using key k hk

/-! ## Classical part -/

/-- A deterministic classical query algorithm: it chooses its next query as a function of the
list of answers received so far, and finally outputs a guess for `s`. -/
structure ClassicalAlgo (n : ℕ) where
  query : List (BV n) → BV n
  output : List (BV n) → BV n

/-- The list of answers received during the first `k` queries. -/
