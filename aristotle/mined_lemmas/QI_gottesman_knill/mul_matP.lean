/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## Bit vectors -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Bitwise `xor` of two bit strings. -/

lemma mul_matP (M : Matrix (Bits n) (Bits n) ℂ) (p : Pauli n) (b b' : Bits n) :
    (M * matP p) b b' = M b (bxor b' p.xs) * (Complex.I ^ (p.ph : ℕ) * sgn p.zs b') := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (bxor b' p.xs)]
  · simp [matP_apply]
  · intro c _ hc
    simp [matP_apply, hc]
  · intro h; exact absurd (Finset.mem_univ _) h

