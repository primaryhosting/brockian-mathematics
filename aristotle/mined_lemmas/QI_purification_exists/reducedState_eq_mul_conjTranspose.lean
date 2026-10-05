import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

namespace QI

/-! ### Basic definitions -/

section Defs

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A density matrix (mixed state): a positive semidefinite matrix of unit trace. -/

lemma reducedState_eq_mul_conjTranspose (ψ : H × K → ℂ) :
    reducedState ψ = amplitudeMatrix ψ * (amplitudeMatrix ψ)ᴴ := by
  ext i j
  simp [reducedState, amplitudeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

end Defs

/-! ### From matrices to linear maps on Euclidean space -/

section Lin

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The linear map on Euclidean space determined by a matrix. -/
