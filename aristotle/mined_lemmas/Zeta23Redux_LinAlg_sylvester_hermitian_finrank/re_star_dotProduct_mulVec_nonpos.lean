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

theorem re_star_dotProduct_mulVec_nonpos (hA : A.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ i, 0 < hA.eigenvalues i → inner ℂ (hA.eigenvectorBasis i) (toLp 2 x) = 0) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0 := by
  rw [star_dotProduct_mulVec_eq_sum_eigenvalues hA x, Complex.ofReal_re]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases le_or_gt (hA.eigenvalues i) 0 with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  · simp [hx i h]

/-- **Sylvester's law of inertia** (Hermitian case, the inequality direction used in the
paper): if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` associated to a Hermitian matrix
`A` is positive definite on a subspace `W`, then `finrank W ≤ posIndex A`, the number of
strictly positive eigenvalues of `A`. -/
