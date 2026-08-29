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

theorem eigenvalue_isReal (H : E →ₗ[ℂ] E) (psi : E) (E₀ : ℂ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hpsi : psi ≠ 0) (heig : H psi = E₀ • psi) :
    (starRingEnd ℂ) E₀ = E₀ := by
  have h1 := hsymm psi psi
  rw [heig, inner_smul_left, inner_smul_right] at h1
  have h2 : (inner ℂ psi psi : ℂ) ≠ 0 := by simpa using hpsi
  exact mul_right_cancel₀ h2 h1

/-- For a stationary state (an eigenvector of a symmetric Hamiltonian), the expectation
value of any commutator `[H, A]` vanishes. -/
