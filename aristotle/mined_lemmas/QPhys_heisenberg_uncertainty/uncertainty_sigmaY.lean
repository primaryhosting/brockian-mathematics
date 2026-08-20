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

lemma uncertainty_sigmaY : uncertainty sigmaY up = 1 := by
  have h : (⟪up, sigmaY up⟫_ℂ) = 0 := by
    simp [up, sigmaY, Matrix.toEuclideanLin, PiLp.inner_apply, EuclideanSpace.single_apply]
  rw [uncertainty, h]
  simp [up, sigmaY, Matrix.toEuclideanLin, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- In this model the hypotheses of `QPhys.heisenberg_uncertainty` hold with `ℏ = 2`
and the bound is attained: `Δx · Δp = 1 = ℏ / 2`. -/
