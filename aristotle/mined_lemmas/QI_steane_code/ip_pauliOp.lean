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

lemma ip_pauliOp (a₁ b₁ a₂ b₂ : V) (f g : V → ℂ) :
    ip (pauliOp a₁ b₁ f) (pauliOp a₂ b₂ g)
      = sgn (dotp b₂ (a₁ + a₂)) *
          ∑ v, sgn (dotp (b₁ + b₂) v) * (starRingEnd ℂ) (f v) * g (v + (a₁ + a₂)) := by
  rw [ip, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight a₁)
      (fun u => (starRingEnd ℂ) (pauliOp a₁ b₁ f u) * pauliOp a₂ b₂ g u)]
  refine Finset.sum_congr rfl ?_
  intro v _
  have hv : (v + a₁) + a₁ = v := by
    rw [add_assoc, V_add_self, add_zero]
  simp only [Equiv.coe_addRight, pauliOp, map_mul, sgn_conj, hv]
  have h2 : (v + a₁) + a₂ = v + (a₁ + a₂) := by rw [add_assoc]
  rw [h2]
  have hsg : sgn (dotp (b₁ + b₂) v) = sgn (dotp b₁ v) * sgn (dotp b₂ v) := by
    rw [dotp_add_left, sgn_add]
  rw [dotp_add_right b₂ v (a₁ + a₂), sgn_add, hsg]
  ring

/-- Character-sum vanishing: if `b` is not orthogonal to the simplex code then the
`b`-twisted overlap of two code states vanishes. -/
