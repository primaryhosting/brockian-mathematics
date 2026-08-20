import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

theorem abs_amp_eq_one_of_constant {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsConstant f) :
    |amp f (zeroStr n)| = 1 := by
  classical
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  by_cases hcase : ∃ x, f x = true
  · obtain ⟨x0, hx0⟩ := hcase
    have hall : ∀ x, f x = true := fun x => (h x x0).trans hx0
    have h1 : (univ.filter fun x : Fin n → Bool => f x = true) = univ := by
      apply Finset.filter_true_of_mem; intro x _; exact hall x
    have h2 : (univ.filter fun x : Fin n → Bool => f x = false) = ∅ := by
      apply Finset.filter_false_of_mem; intro x _; simp [hall x]
    have hval : amp f (zeroStr n) = -1 := by
      rw [amp_zeroStr, h1, h2]
      have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by simp
      simp only [Finset.card_empty, Nat.cast_zero, zero_sub, hcard]
      field_simp
    rw [hval]
    norm_num
  · push_neg at hcase
    have hall : ∀ x, f x = false := by
      intro x; cases hx : f x
      · rfl
      · exact absurd hx (hcase x)
    have h1 : (univ.filter fun x : Fin n → Bool => f x = true) = ∅ := by
      apply Finset.filter_false_of_mem; intro x _; simp [hall x]
    have h2 : (univ.filter fun x : Fin n → Bool => f x = false) = univ := by
      apply Finset.filter_true_of_mem; intro x _; exact hall x
    have hval : amp f (zeroStr n) = 1 := by
      rw [amp_zeroStr, h1, h2]
      have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by simp
      simp only [Finset.card_empty, Nat.cast_zero, sub_zero, hcard]
      field_simp
    rw [hval]
    norm_num

/-- **Deutsch–Jozsa.**  For a promise function `f : {0,1}^n → {0,1}` which is either
constant or balanced, one run of the circuit `H^{⊗n} ∘ O_f ∘ H^{⊗n}|0…0⟩` — which uses
the oracle `O_f` exactly once — decides which:  the all-zeros outcome has probability
`1` exactly when `f` is constant, and probability `0` exactly when `f` is balanced. -/
