import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma w_pow_mod {a b : ℕ} (h : a % 20 = b % 20) : w ^ a = w ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 20]
  conv_rhs => rw [← Nat.div_add_mod b 20]
  simp [pow_add, pow_mul, w_pow_20, h]

