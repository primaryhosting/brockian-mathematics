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

lemma conj_expectation (A : E →ₗ[ℂ] E) (hA : ∀ x y : E, inner ℂ (A x) y = inner ℂ x (A y))
    (psi : E) : conj (inner ℂ psi (A psi)) = inner ℂ psi (A psi) := by
  rw [inner_conj_symm (A psi) psi, hA]

/-- Expansion of the inner product of two vectors centred by (real) expectation values. -/
