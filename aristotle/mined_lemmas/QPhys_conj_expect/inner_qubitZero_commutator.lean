/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator `A` on a complex inner product space is *symmetric* (an observable) if
`⟪A x, y⟫ = ⟪x, A y⟫` for all `x y`. -/

lemma inner_qubitZero_commutator :
    ⟪qubitZero, sigmaX (sigmaY qubitZero) - sigmaY (sigmaX qubitZero)⟫_ℂ = 2 * Complex.I := by
  simp [sigmaX, sigmaY, qubitZero, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.vecHead, Matrix.vecTail, Matrix.col]
  ring

/-- Non-vacuity check: for the qubit observables `σₓ`, `σ_y` in the state `|0⟩` the
Robertson bound gives the nontrivial inequality `Δσₓ · Δσ_y ≥ 1`. -/
