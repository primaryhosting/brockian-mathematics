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

lemma zeta_pow_modEq {a b : ℕ} (h : a ≡ b [MOD 15]) : zeta ^ a = zeta ^ b := by
  rcases le_total a b with hab | hab
  · exact zeta_pow_modEq_of_le hab h
  · exact (zeta_pow_modEq_of_le hab h.symm).symm

