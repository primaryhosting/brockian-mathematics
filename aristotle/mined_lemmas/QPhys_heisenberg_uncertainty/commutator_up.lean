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

lemma commutator_up :
    sigmaX (sigmaY up) - sigmaY (sigmaX up) = (Complex.I * ((2 : ℝ) : ℂ)) • up := by
  ext i
  fin_cases i
  · simp [sigmaX, sigmaY, up, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply]
    ring
  · simp [sigmaX, sigmaY, up, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply]

