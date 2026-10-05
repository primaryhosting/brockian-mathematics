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

lemma cxf_bxor (j k : Fin n) (u v : Bits n) :
    cxf j k (bxor u v) = bxor (cxf j k u) (cxf j k v) := by
  funext i
  simp only [cxf, bxor_apply, condVec_apply]
  cases hik : decide (i = k) <;> cases u j <;> cases v j <;> simp [Bool.xor_comm]

