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

lemma pauli_pair_mem (i j : Fin 9) (x₁ z₁ x₂ z₂ : Bits)
    (h₁ : ∀ k, k ≠ i → x₁ k = 0 ∧ z₁ k = 0)
    (h₂ : ∀ k, k ≠ j → x₂ k = 0 ∧ z₂ k = 0) :
    pauli x₁ z₁ * pauli x₂ z₂ ∈ corrSub := by
  have hsupp : ∀ k, k ≠ i → k ≠ j → (x₁ + x₂) k = 0 ∧ (z₁ + z₂) k = 0 := by
    intro k hki hkj
    have a := h₁ k hki
    have b := h₂ k hkj
    simp [a.1, a.2, b.1, b.2]
  obtain ⟨c, hc⟩ := sandwich_pauli i j (x₁ + x₂) (z₁ + z₂) hsupp
  refine Submodule.mem_comap.mpr ?_
  rw [sandwichMap_apply, pauli_mul, Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩

