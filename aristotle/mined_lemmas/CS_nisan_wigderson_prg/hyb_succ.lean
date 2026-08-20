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

lemma hyb_succ {n m ℓ : ℕ} (S : Fin m → Fin n → Fin ℓ) (f : (Fin n → Bool) → Bool)
    {t : ℕ} (ht : t < m) (x : Fin ℓ → Bool) (y : Fin m → Bool) :
    hyb S f (t + 1) x y
      = hyb S f t x (Function.update y ⟨t, ht⟩ (nwGen S f x ⟨t, ht⟩)) := by
  funext i
  simp only [hyb]
  rcases lt_trichotomy (i : ℕ) t with h | h | h
  · simp [h, Nat.lt_succ_of_lt h]
  · have hi : i = (⟨t, ht⟩ : Fin m) := Fin.ext h
    subst hi
    simp
  · have hne : i ≠ (⟨t, ht⟩ : Fin m) := by
      intro hh; rw [hh] at h; exact absurd h (lt_irrefl t)
    have h1 : ¬ ((i : ℕ) < t + 1) := by omega
    simp [h1, Nat.not_lt.mpr h.le, Function.update_of_ne hne]

/-- Yao's next-bit predictor step: the hybrid gap at step `t` is exactly the advantage of the
predictor built from `D`. -/
