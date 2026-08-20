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

lemma pick_three {α : Type*} [DecidableEq α] (i j a b c : α)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (a ≠ i ∧ a ≠ j) ∨ (b ≠ i ∧ b ≠ j) ∨ (c ≠ i ∧ c ≠ j) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  by_cases hai : a = i
  · have hbi : b ≠ i := fun h => hab (hai.trans h.symm)
    have hci : c ≠ i := fun h => hac (hai.trans h.symm)
    exact hbc ((h2 hbi).trans (h3 hci).symm)
  · have haj := h1 hai
    by_cases hbi : b = i
    · have hci : c ≠ i := fun h => hbc (hbi.trans h.symm)
      exact hac (haj.trans (h3 hci).symm)
    · exact hab (haj.trans (h2 hbi).symm)

/-- The syndrome of the Pauli error `X^x Z^z` against the stabilizer element with
exponent vector `t`. -/
