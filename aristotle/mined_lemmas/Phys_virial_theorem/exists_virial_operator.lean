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

theorem exists_virial_operator (H A T : E →ₗ[ℂ] E) :
    ∀ x : E, H (A x) - A (H x)
      = Complex.I • ((2 : ℂ) • T x
          - ((2 : ℂ) • T + Complex.I • (H ∘ₗ A - A ∘ₗ H)) x) := by
  intro x
  simp [LinearMap.sub_apply, smul_smul, Complex.I_mul_I]

/-! ## A concrete instance: the one-dimensional harmonic oscillator ground state -/

/-- The (normalized) ground state of the one–dimensional harmonic oscillator
`H = -½ d²/dx² + ½ x²`. -/
