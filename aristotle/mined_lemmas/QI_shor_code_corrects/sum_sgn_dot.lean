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

lemma sum_sgn_dot (z : Bits) : ∑ v : Bits, sgn (dot z v) = if z = 0 then 512 else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp [dot_zero_left, sgn_zero]
  · rw [if_neg hz]
    obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (funext hc)
    have hzk : z k = 1 := (zmod_two_cases (z k)).resolve_left hk
    have hshift : ∑ v : Bits, sgn (dot z (v + unit k)) = ∑ v : Bits, sgn (dot z v) :=
      Equiv.sum_comp (Equiv.addRight (unit k)) (fun v => sgn (dot z v))
    have hval : ∀ v : Bits, sgn (dot z (v + unit k)) = - sgn (dot z v) := by
      intro v
      rw [dot_add_right, sgn_add, dot_comm z (unit k), dot_unit_left, hzk]
      simp [sgn]
    rw [Finset.sum_congr rfl (fun v _ => hval v), Finset.sum_neg_distrib] at hshift
    linear_combination (-1/2 : ℂ) * hshift

