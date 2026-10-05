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

lemma zeta_pow_modEq_of_le {a b : ℕ} (hab : a ≤ b) (h : a ≡ b [MOD 15]) :
    zeta ^ a = zeta ^ b := by
  obtain ⟨t, ht⟩ : 15 ∣ (b - a) := (Nat.modEq_iff_dvd' hab).mp h
  have hb : b = a + 15 * t := by omega
  subst hb
  rw [pow_add, pow_mul, zeta_pow_fifteen, one_pow, mul_one]

