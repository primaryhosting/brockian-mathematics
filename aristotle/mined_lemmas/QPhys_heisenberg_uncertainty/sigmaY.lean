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

noncomputable def sigmaY : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, -Complex.I; Complex.I, 0]

/-- The spin-up state. -/
