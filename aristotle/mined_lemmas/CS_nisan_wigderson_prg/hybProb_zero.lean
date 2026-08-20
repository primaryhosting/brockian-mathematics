/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace CS

/-! ### Basic probabilistic vocabulary

All probabilities are uniform probabilities over finite types, expressed as expectations
of `{0,1}`-valued indicator functions. -/

/-- The `{0,1}`-valued indicator of a boolean. -/

lemma hybProb_zero {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) : hybProb S f D 0 = pr D := by
  rw [hybProb, pr_prod]
  have h : ∀ (x : Fin ℓ → Bool) (y : Fin m → Bool), hyb S f 0 x y = y := by
    intro x y; funext i; simp [hyb]
  simp only [h]
  rw [Finset.expect_const univ_nonempty]
  rfl

