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

lemma matP_mul (M : Matrix (Bits n) (Bits n) ℂ) (p : Pauli n) (b b' : Bits n) :
    (matP p * M) b b' =
      (Complex.I ^ (p.ph : ℕ) * sgn p.zs (bxor b p.xs)) * M (bxor b p.xs) b' := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (bxor b p.xs)]
  · simp [matP_apply]
  · intro c _ hc
    have : ¬ (b = bxor c p.xs) := by
      intro h; exact hc (by rw [h]; simp)
    simp [matP_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Clifford gates -/

/-- The generators of the Clifford group: Hadamard, phase gate, and CNOT (on distinct wires). -/
inductive Gate (n : ℕ)
  | H : Fin n → Gate n
  | S : Fin n → Gate n
  | CX (j k : Fin n) (h : j ≠ k) : Gate n

/-- `1/√2`, the normalisation of the Hadamard gate. -/
