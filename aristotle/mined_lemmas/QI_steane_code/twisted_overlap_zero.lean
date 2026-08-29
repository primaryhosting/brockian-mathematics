import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the statement that the seven–qubit Steane CSS code corrects an
arbitrary error on a single qubit, in the standard Knill–Laflamme form:

for any two single–qubit Pauli errors `E₁`, `E₂` there is a constant `c`
(depending only on the errors) such that
`⟪E₁ ψ, E₂ φ⟫ = c * ⟪ψ, φ⟫` for all code states `ψ, φ`.

Everything is set up concretely.  The `2^7`-dimensional state space is modelled
as the space of functions `V → ℂ` where `V = Fin 7 → ZMod 2` indexes the
computational basis.  Pauli operators `X^a Z^b` act by
`(X^a Z^b) |v⟩ = (-1)^{b·v} |v + a⟩`, i.e. by `pauliOp`.  The Steane code space
is spanned by the two logical basis states
`|0_L⟩ = Σ_{v ∈ C} |v⟩` and `|1_L⟩ = Σ_{v ∈ C^⊥ \ C} |v⟩`,
where `C` is the `[7,3]` simplex code (the row span of the Hamming parity check
matrix `Hm`) and `C^⊥` is the `[7,4]` Hamming code.  Concretely a codeword `v`
lies in `C^⊥` iff all three parity checks vanish (`InD v`), and it lies in `C`
iff moreover it has even weight (`par v = 0`).
-/

namespace QI

/-- Bit strings of length seven: the index set of the computational basis. -/
abbrev V := Fin 7 → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

lemma twisted_overlap_zero {b : V} (k : Fin 3) (hk : dotp (Hm k) b = 1) (α β γ δ : ℂ) :
    ∑ v, sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v) * codeState γ δ v = 0 := by
  set w : V := Hm k with hw
  set S := ∑ v, sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v) * codeState γ δ v with hS
  have key : S = -S := by
    conv_lhs =>
      rw [hS, ← Equiv.sum_comp (Equiv.addRight w)
        (fun v => sgn (dotp b v) * (starRingEnd ℂ) (codeState α β v) * codeState γ δ v)]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro v _
    have hbw : dotp b w = 1 := by rw [dotp_comm]; exact hk
    have h1 : sgn (dotp b (v + w)) = - sgn (dotp b v) := by
      rw [dotp_add_right, sgn_add, hbw, sgn_one]
      ring
    have h2 : codeState α β (v + w) = codeState α β v :=
      codeState_shift α β (InD_Hm k) (Hm_even k) v
    have h3 : codeState γ δ (v + w) = codeState γ δ v :=
      codeState_shift γ δ (InD_Hm k) (Hm_even k) v
    simp only [Equiv.coe_addRight, h1, h2, h3]
    ring
  have h2 : (2 : ℂ) * S = 0 := by linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- **The Steane code corrects an arbitrary single–qubit error.**

For any two single–qubit Pauli errors `E₁ = X^{a₁} Z^{b₁}` and
`E₂ = X^{a₂} Z^{b₂}` there is a scalar `c` such that
`⟪E₁ ψ, E₂ φ⟫ = c ⟪ψ, φ⟫` for all states `ψ, φ` of the code space.  This is the
Knill–Laflamme error–correction criterion for the error set consisting of all
single–qubit Paulis, so the seven–qubit Steane code corrects any single–qubit
error. -/
