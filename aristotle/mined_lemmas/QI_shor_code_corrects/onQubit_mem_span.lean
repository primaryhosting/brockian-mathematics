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

lemma onQubit_mem_span (i j : Fin 9) (E F : Matrix (ZMod 2) (ZMod 2) ℂ) :
    onQubit i E * onQubit j F ∈ corrSub := by
  rw [onQubit_decomp i E, onQubit_decomp j F]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  repeat' refine Submodule.add_mem _ ?_ ?_
  all_goals
    refine Submodule.smul_mem _ _ ?_
    exact pauli_pair_mem i j _ _ _ _ (by intro k hk; simp [unit, hk])
      (by intro k hk; simp [unit, hk])

/-- **The nine-qubit Shor code corrects an arbitrary single-qubit error.**

`shorProj` is the projector onto the code space, which is two-dimensional
(`QI.shorProj_trace`, together with `QI.shorProj_idem` and `QI.shorProj_conjTranspose`).
For arbitrary single-qubit operators `E` acting on qubit `i` and `F` acting on qubit `j`,
the Knill–Laflamme condition `P Eᴴ F P = c • P` holds; by the Knill–Laflamme theorem this is
exactly the statement that the code corrects an arbitrary error supported on a single qubit. -/
