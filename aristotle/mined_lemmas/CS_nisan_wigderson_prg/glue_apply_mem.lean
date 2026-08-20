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

lemma glue_apply_mem {n ℓ : ℕ} {σ : Fin n → Fin ℓ} (hσ : Function.Injective σ)
    (z : Fin n → Bool) (x0 : Fin ℓ → Bool) (k : Fin n) : glue σ z x0 (σ k) = z k := by
  have h : ∃ k', σ k' = σ k := ⟨k, rfl⟩
  simp only [glue, dif_pos h]
  congr 1
  exact hσ h.choose_spec

