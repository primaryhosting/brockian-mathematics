/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace QPhys

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

theorem pauliY_symm (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (pauliY x) y = inner ℂ x (pauliY y) := by
  simp [pauliY, PiLp.inner_apply, Fin.sum_univ_two, Complex.ext_iff]
  exact ⟨by ring, by ring⟩

