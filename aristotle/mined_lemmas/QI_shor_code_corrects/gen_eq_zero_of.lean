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

lemma gen_eq_zero_of (t : Gen) (hx : xPart t = 0) (hz : zPart t = 0) : t = 0 := by
  have h0 : t 0 = 0 := by simpa [zPart] using congrFun hz 0
  have h1 : t 1 = 0 := by simpa [zPart] using congrFun hz 2
  have h2 : t 2 = 0 := by simpa [zPart] using congrFun hz 3
  have h3 : t 3 = 0 := by simpa [zPart] using congrFun hz 5
  have h4 : t 4 = 0 := by simpa [zPart] using congrFun hz 6
  have h5 : t 5 = 0 := by simpa [zPart] using congrFun hz 8
  have h6 : t 6 = 0 := by simpa [xPart] using congrFun hx 0
  have h7 : t 7 = 0 := by simpa [xPart] using congrFun hx 8
  funext m
  fin_cases m <;> simp only [Pi.zero_apply] <;>
    first
      | exact h0 | exact h1 | exact h2 | exact h3
      | exact h4 | exact h5 | exact h6 | exact h7

/-- The code space is two-dimensional: the projector has trace `2`. -/
