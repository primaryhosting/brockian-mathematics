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

theorem balanced_of_amp_eq_zero {n : ℕ} (f : (Fin n → Bool) → Bool)
    (h : amp f (zeroStr n) = 0) : IsBalanced f := by
  rw [amp_zeroStr] at h
  have hpow : (1 / 2 ^ n : ℝ) ≠ 0 := by positivity
  have h2 : ((univ.filter fun x : Fin n → Bool => f x = false).card : ℝ)
      - ((univ.filter fun x => f x = true).card : ℝ) = 0 := by
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' hpow
    · exact h'
  have h3 : (univ.filter fun x : Fin n → Bool => f x = false).card
      = (univ.filter fun x => f x = true).card := by
    have := sub_eq_zero.1 h2
    exact_mod_cast this
  have hc := card_true_add_card_false f
  unfold IsBalanced
  omega

/-- **Constant case**: the all-zeros outcome occurs with probability one. -/
