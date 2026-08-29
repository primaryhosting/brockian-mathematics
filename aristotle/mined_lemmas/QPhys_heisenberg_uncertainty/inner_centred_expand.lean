/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open ComplexConjugate

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value of a symmetric operator in a state is real. -/

lemma inner_centred_expand (x y psi : E) (a b : ℂ) (hpp : (inner ℂ psi psi : ℂ) = 1)
    (hxp : (inner ℂ x psi : ℂ) = a) (hpy : (inner ℂ psi y : ℂ) = b) (hca : conj a = a) :
    (inner ℂ (x - a • psi) (y - b • psi) : ℂ) = inner ℂ x y - a * b := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hxp, hpy, hpp,
    hca]
  ring

/-- **Heisenberg uncertainty principle.**  For symmetric linear operators `A` and `B` on a
complex inner product space satisfying the canonical commutation relation `[A,B]ψ = i ħ ψ`
at a normalized state `ψ`, the product of the standard deviations
`Δ_A = ‖(A - ⟪ψ, Aψ⟫)ψ‖` and `Δ_B = ‖(B - ⟪ψ, Bψ⟫)ψ‖` is at least `ħ/2`. -/
