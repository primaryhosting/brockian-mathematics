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

lemma pauliMatrix_apply {n : ℕ} (p : Pauli n) (a b : Bits n) :
    pauliMatrix p a b = ph p.s * (if a = b + p.x then psign (ip p.z b) else 0) := by
  simp only [pauliMatrix, Matrix.smul_apply, smul_eq_mul, tp, xz]
  congr 1
  rw [prod_ite_zero (fun q => a q = b q + p.x q) (fun q => psign (p.z q * b q))]
  congr 1
  · simp only [eq_iff_iff]
    constructor
    · intro h; funext q; simpa using h q
    · intro h q; rw [h]; simp
  · rw [ip, psign_sum]

/-- The Clifford generators: Hadamard, phase gate, controlled-`Z`. -/
inductive Gate (n : ℕ)
  | H : Fin n → Gate n
  | S : Fin n → Gate n
  | CZ : Fin n → Fin n → Gate n

/-- The unitary matrix of a Clifford generator. -/
