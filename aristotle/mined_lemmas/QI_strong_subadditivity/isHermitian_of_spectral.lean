import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part I: Functional calculus for Hermitian matrices -/


theorem isHermitian_of_spectral {M U : Matrix n n ℂ} {μ : n → ℝ}
    (hM : M = U * diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U) : M.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [hM]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose,
    Matrix.star_eq_conjTranspose, star_ofReal_fun]

