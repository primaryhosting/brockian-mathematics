import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma P13_apply (j k : Fin 13) : P13 j k = (qc k) ^ (j : ℕ) := by
  simp only [P13, Matrix.vandermonde_apply, qc, ← pow_mul]
  rw [Nat.mul_comm]

