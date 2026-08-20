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

lemma expect_glue {n ℓ : ℕ} {σ : Fin n → Fin ℓ} (hσ : Function.Injective σ)
    (F : (Fin ℓ → Bool) → ℝ) :
    (𝔼 (x : Fin ℓ → Bool), F x) = 𝔼 (z : Fin n → Bool), 𝔼 (x0 : Fin ℓ → Bool), F (glue σ z x0) := by
  have h1 : (𝔼 (p : (Fin n → Bool) × (Fin ℓ → Bool)), F (glue σ p.1 p.2))
      = 𝔼 (z : Fin n → Bool), 𝔼 (x0 : Fin ℓ → Bool), F (glue σ z x0) := by
    have h := Finset.expect_product' (univ : Finset (Fin n → Bool))
      (univ : Finset (Fin ℓ → Bool)) fun z x0 => F (glue σ z x0)
    rw [Finset.univ_product_univ] at h
    exact h
  have h2 : (𝔼 (p : (Fin n → Bool) × (Fin ℓ → Bool)), F (glue σ p.1 p.2))
      = 𝔼 (q : (Fin ℓ → Bool) × (Fin n → Bool)), F q.1 :=
    Finset.expect_equiv (glueEquiv hσ) (by simp) fun p _ => rfl
  have h3 : (𝔼 (q : (Fin ℓ → Bool) × (Fin n → Bool)), F q.1) = 𝔼 (x : Fin ℓ → Bool), F x := by
    have h := Finset.expect_product' (univ : Finset (Fin ℓ → Bool))
      (univ : Finset (Fin n → Bool)) fun x _v => F x
    rw [Finset.univ_product_univ] at h
    rw [h]
    exact Finset.expect_congr rfl fun x _ => Finset.expect_const univ_nonempty _
  rw [← h1, h2, h3]

/-- Averaging over a boolean vector equals averaging the two possible values of one coordinate. -/
