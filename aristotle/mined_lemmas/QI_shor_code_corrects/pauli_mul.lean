/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 8000

open scoped BigOperators Matrix

/-!
## Setup

We work with operators on nine qubits as matrices indexed by bit strings `Bits = Fin 9 → ZMod 2`
(so the Hilbert space is `ℂ^(2^9)`).  For `x z : Bits`, `pauli x z` is the Pauli operator
`X^x Z^z`, acting on basis states by `|v⟩ ↦ (-1)^(z·v) |v + x⟩`.

The Shor code is the stabilizer code with the eight generators
`Z₁Z₂, Z₂Z₃, Z₄Z₅, Z₅Z₆, Z₇Z₈, Z₈Z₉, X₁X₂X₃X₄X₅X₆, X₄X₅X₆X₇X₈X₉`;
`shorStab t` is the stabilizer element with exponent vector `t : Fin 8 → ZMod 2`, and
`shorProj = (1/256) ∑ t, shorStab t` is the projector onto the code space.

`onQubit i M` is the operator acting as the arbitrary `2 × 2` matrix `M` on qubit `i` and as the
identity on the other eight qubits; these are exactly the single-qubit errors.  The main theorem
`QI.shor_code_corrects` is the Knill–Laflamme error-correction condition for this error set.
-/

namespace QI

/-- Computational basis labels of nine qubits: bit strings of length `9`. -/
abbrev Bits := Fin 9 → ZMod 2

/-- Index type for the elements of the stabilizer group of the Shor code:
one `ZMod 2` exponent for each of the eight stabilizer generators. -/
abbrev Gen := Fin 8 → ZMod 2

/-- The sign `(-1)^a` for `a : ZMod 2`. -/

lemma pauli_mul (x₁ z₁ x₂ z₂ : Bits) :
    pauli x₁ z₁ * pauli x₂ z₂ = sgn (dot z₁ x₂) • pauli (x₁ + x₂) (z₁ + z₂) := by
  ext u v
  rw [Matrix.mul_apply, Finset.sum_eq_single (v + x₂)]
  · simp only [pauli_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    by_cases h : u = v + (x₁ + x₂)
    · rw [if_pos (by rw [h]; abel), if_pos h, dot_add_right, dot_add_left, sgn_add, sgn_add]
      ring
    · rw [if_neg (by intro hh; exact h (by rw [hh]; abel)), if_neg h]; ring
  · intro b _ hb
    simp only [pauli_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The stabilizer group -/

