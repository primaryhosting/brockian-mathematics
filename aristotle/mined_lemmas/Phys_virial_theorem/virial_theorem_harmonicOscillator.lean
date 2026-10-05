import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Phys

open Complex MeasureTheory Filter Topology

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

theorem virial_theorem_harmonicOscillator :
    2 * (∫ x : ℝ, psiHO x * (-(1 / 2) * deriv (deriv psiHO) x))
      = ∫ x : ℝ, psiHO x * ((x * deriv VHO x) * psiHO x) := by
  rw [psiHO_kinetic, psiHO_virialExpectation]
  norm_num

end Phys

