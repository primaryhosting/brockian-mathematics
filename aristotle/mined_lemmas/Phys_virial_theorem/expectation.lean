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

noncomputable def expectation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) (psi : E) : ℂ :=
  inner ℂ psi (A psi)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An eigenvalue of a symmetric operator, on a nonzero eigenvector, is real. -/
