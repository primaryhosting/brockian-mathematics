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

lemma hybProb_card {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) : hybProb S f D m = pr fun x => D (nwGen S f x) := by
  rw [hybProb, pr_prod]
  have h : ∀ (x : Fin ℓ → Bool) (y : Fin m → Bool), hyb S f m x y = nwGen S f x := by
    intro x y; funext i; simp [hyb, i.isLt]
  simp only [h]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [Finset.expect_const univ_nonempty]

