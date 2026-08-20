/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-- The sign `(-1)^(f x)` attached to a Boolean value. -/

lemma djSum_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, sign (f x)) = 2 ^ n - 2 * (numTrue f : ℚ) := by
  have h : ∀ x : Fin n → Bool, sign (f x) = 1 - 2 * (if f x = true then (1 : ℚ) else 0) := by
    intro x
    unfold sign
    cases f x <;> norm_num
  rw [Finset.sum_congr rfl fun x _ => h x]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [numTrue, card_domain]

