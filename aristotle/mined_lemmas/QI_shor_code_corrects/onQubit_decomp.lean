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

lemma onQubit_decomp (i : Fin 9) (M : Matrix (ZMod 2) (ZMod 2) ℂ) :
    onQubit i M =
      ((M 0 0 + M 1 1) / 2) • pauli 0 0
        + ((M 0 1 + M 1 0) / 2) • pauli (unit i) 0
        + ((M 0 0 - M 1 1) / 2) • pauli 0 (unit i)
        + ((M 1 0 - M 0 1) / 2) • pauli (unit i) (unit i) := by
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, pauli_apply, onQubit_apply, smul_eq_mul,
    add_zero, dot_zero_left, dot_unit_left, sgn_zero]
  by_cases h : ∀ k, k ≠ i → u k = v k
  · simp only [if_pos h]
    rcases eq_or_ne (u i) (v i) with h2 | h2
    · have huv : u = v := by
        ext k; rcases eq_or_ne k i with rfl | hk
        · exact h2
        · exact h k hk
      have hne : ¬ (u = v + unit i) := by
        rw [eq_add_unit_iff]
        rintro ⟨-, hh⟩
        rw [h2] at hh
        exact (by decide : ∀ a : ZMod 2, ¬ (a = a + 1)) (v i) hh
      simp only [if_pos huv, if_neg hne]
      rcases zmod_two_cases (v i) with hv | hv <;> rw [h2, hv] <;> norm_num [sgn] <;> ring
    · have hui : u i = v i + 1 := by
        rcases zmod_two_cases (u i) with h3 | h3 <;> rcases zmod_two_cases (v i) with h4 | h4
        · exact absurd (h3.trans h4.symm) h2
        · rw [h3, h4]; decide
        · rw [h3, h4]; decide
        · exact absurd (h3.trans h4.symm) h2
      have hyes : u = v + unit i := (eq_add_unit_iff u v i).2 ⟨h, hui⟩
      have hno : ¬ (u = v) := fun hh => h2 (by rw [hh])
      simp only [if_neg hno, if_pos hyes]
      rcases zmod_two_cases (v i) with hv | hv <;>
        simp only [hui, hv, show (0 : ZMod 2) + 1 = 1 from by decide,
          show (1 : ZMod 2) + 1 = 0 from by decide] <;>
        norm_num [sgn] <;> ring
  · have h1 : ¬ (u = v) := fun hh => h (fun k _ => by rw [hh])
    have h2 : ¬ (u = v + unit i) := fun hh => h ((eq_add_unit_iff u v i).1 hh).1
    simp only [if_neg h, if_neg h1, if_neg h2]
    ring

