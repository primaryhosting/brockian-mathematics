import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma zeta_pow_inj {a b : ℕ} (ha : a < 15) (hb : b < 15) (h : zeta ^ a = zeta ^ b) : a = b := by
  have key : ∀ a b : ℕ, a ≤ b → b < 15 → zeta ^ a = zeta ^ b → a = b := by
    intro a b hab hb h
    have h1 : zeta ^ a * zeta ^ (b - a) = zeta ^ a * 1 := by
      rw [mul_one, ← pow_add, show a + (b - a) = b by omega]
      exact h.symm
    have h2 : zeta ^ (b - a) = 1 := mul_left_cancel₀ (pow_ne_zero _ zeta_ne_zero) h1
    have h3 := (zeta_prim.pow_eq_one_iff_dvd _).mp h2
    omega
  rcases le_total a b with hab | hab
  · exact key a b hab hb h
  · exact (key b a hab ha h.symm).symm

/-- The character values `ζ ^ i` for `i : Fin 15`. -/
