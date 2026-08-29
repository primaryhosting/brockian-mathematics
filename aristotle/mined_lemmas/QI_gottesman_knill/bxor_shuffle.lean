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

lemma bxor_shuffle (a x c1 c2 : Bits n) :
    bxor (bxor (bxor a x) c1) (bxor x c2) = bxor a (bxor c1 c2) := by
  funext i
  simp only [bxor_apply]
  exact bool_xor_shuffle (a i) (x i) (c1 i) (c2 i)

