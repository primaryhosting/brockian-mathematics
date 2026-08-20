import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The uncertainty (standard deviation) of a symmetric operator `A` in the state `ψ`:
the norm of `A ψ` after subtracting its expectation value `⟪ψ, A ψ⟫`. -/

lemma uncertainty_sigmaX : uncertainty sigmaX up = 1 := by
  have h : (⟪up, sigmaX up⟫_ℂ) = 0 := by
    simp [up, sigmaX, Matrix.toEuclideanLin, PiLp.inner_apply, EuclideanSpace.single_apply]
  rw [uncertainty, h]
  simp [up, sigmaX, Matrix.toEuclideanLin, EuclideanSpace.norm_eq, Fin.sum_univ_two]

