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

lemma sigmaY_symm (u v : EuclideanSpace ℂ (Fin 2)) : ⟪sigmaY u, v⟫_ℂ = ⟪u, sigmaY v⟫_ℂ := by
  simp [sigmaY, Matrix.toEuclideanLin, PiLp.inner_apply, Fin.sum_univ_two, dotProduct]
  ring

/-- The canonical commutation relation `[σx, σy] |↑⟩ = i · 2 · |↑⟩`. -/
