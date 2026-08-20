import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix WithLp Finset

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The *positive index* of a Hermitian matrix `A`: the number of strictly positive
eigenvalues of `A` (counted with multiplicity, i.e. the number of indices `i` with
`hA.eigenvalues i > 0`).  It depends on `A` only, but is phrased in terms of the
hermiticity witness `hA` since Mathlib's `Matrix.IsHermitian.eigenvalues` is. -/

theorem star_dotProduct_mulVec_eq_sum_eigenvalues (hA : A.IsHermitian) (x : Fin d → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) =
      ((∑ i, hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x)‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_mulVec_eq_sum_eigenvalues hA (toLp 2 x)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm] at h
  rw [h]
  push_cast
  rfl

/-- If all the "positive" eigen-coordinates of `x` vanish, then the Hermitian form is
nonpositive at `x`. -/
