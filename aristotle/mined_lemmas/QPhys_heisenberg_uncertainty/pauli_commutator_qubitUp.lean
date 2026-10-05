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

theorem pauli_commutator_qubitUp :
    inner ℂ qubitUp (pauliX (pauliY qubitUp)) - inner ℂ qubitUp (pauliY (pauliX qubitUp))
      = ((2 : ℝ) : ℂ) * Complex.I := by
  simp [qubitUp, pauliX, pauliY, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- A concrete, non-vacuous instance of the uncertainty relation: for the spin-up qubit
state the product of the `σx` and `σy` uncertainties is at least `1 = ℏ/2` with `ℏ = 2`. -/
