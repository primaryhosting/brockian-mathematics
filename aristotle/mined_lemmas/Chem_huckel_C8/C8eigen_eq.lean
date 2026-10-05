import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma C8eigen_eq (k : Fin 8) :
    C8eigen k = zeta8 ^ (k : ℕ) + (zeta8 ^ (k : ℕ))⁻¹ := by
  rw [C8eigen, zeta8_pow_eq, exp_add_inv]

/-- The basic cyclic identity: for an 8-th root of unity `w`,
`w^(i+1) + w^(i-1) = w^i * (w + w⁻¹)`, with exponents taken cyclically. -/
