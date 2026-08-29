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

lemma I_pow_fin4_add (a b : Fin 4) :
    Complex.I ^ ((a + b : Fin 4) : ℕ) = Complex.I ^ (a : ℕ) * Complex.I ^ (b : ℕ) := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.add_def, pow_succ, Complex.I_mul_I]

