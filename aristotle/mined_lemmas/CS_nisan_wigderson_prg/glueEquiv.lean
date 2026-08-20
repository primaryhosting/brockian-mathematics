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

noncomputable def glueEquiv {n ℓ : ℕ} {σ : Fin n → Fin ℓ} (hσ : Function.Injective σ) :
    ((Fin n → Bool) × (Fin ℓ → Bool)) ≃ ((Fin ℓ → Bool) × (Fin n → Bool)) where
  toFun p := (glue σ p.1 p.2, fun k => p.2 (σ k))
  invFun q := (fun k => q.1 (σ k), glue σ q.2 q.1)
  left_inv := by
    rintro ⟨z, x0⟩
    refine Prod.ext (funext fun k => glue_apply_mem hσ z x0 k) ?_
    simp only
    funext i
    by_cases h : ∃ k, σ k = i
    · obtain ⟨k, rfl⟩ := h
      simp [glue_apply_mem hσ]
    · push_neg at h
      rw [glue_apply_not_mem _ _ h, glue_apply_not_mem _ _ h]
  right_inv := by
    rintro ⟨x, v⟩
    refine Prod.ext ?_ (funext fun k => glue_apply_mem hσ v x k)
    simp only
    funext i
    by_cases h : ∃ k, σ k = i
    · obtain ⟨k, rfl⟩ := h
      simp [glue_apply_mem hσ]
    · push_neg at h
      rw [glue_apply_not_mem _ _ h, glue_apply_not_mem _ _ h]

/-- Averaging over the seed can be done by first averaging over the bits sitting in the
range of an injective map `σ` and then over the remaining bits. -/
