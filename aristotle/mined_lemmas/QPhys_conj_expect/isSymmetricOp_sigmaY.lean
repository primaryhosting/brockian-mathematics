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

lemma isSymmetricOp_sigmaY : IsSymmetricOp sigmaY := by
  have h : (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    simp [Matrix.IsHermitian, ← Matrix.ext_iff, Fin.forall_fin_two]
  exact Matrix.isHermitian_iff_isSymmetric.mp h

