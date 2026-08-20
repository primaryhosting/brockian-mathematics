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

lemma sigmaX_symm (u v : EuclideanSpace ℂ (Fin 2)) : ⟪sigmaX u, v⟫_ℂ = ⟪u, sigmaX v⟫_ℂ := by
  simp [sigmaX, Matrix.toEuclideanLin, PiLp.inner_apply, Fin.sum_univ_two, dotProduct]
  ring

