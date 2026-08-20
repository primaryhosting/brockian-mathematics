/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma tp_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    tp (fun q => c q • M q) = (∏ q, c q) • tp M := by
  ext a b
  simp [tp, Finset.prod_mul_distrib]

/-- Pointwise commutation relations tensor up. -/
