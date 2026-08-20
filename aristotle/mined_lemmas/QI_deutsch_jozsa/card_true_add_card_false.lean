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

lemma card_true_add_card_false {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (univ.filter fun x => f x = true).card + (univ.filter fun x => f x = false).card = 2 ^ n := by
  classical
  have h : (univ.filter fun x : Fin n → Bool => f x = false)
      = univ.filter fun x => ¬ (f x = true) := by
    apply Finset.filter_congr
    intro x _
    cases hx : f x <;> simp_all
  rw [h, Finset.card_filter_add_card_filter_not]
  simp

/-- The key sum: `∑_x (-1)^{f x} = #{f = false} - #{f = true}`. -/
