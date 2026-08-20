import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, A x⟫` attached to a complex matrix `A`,
seen as an operator on `EuclideanSpace ℂ (Fin d)`. -/

lemma quadForm_eq {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadForm A x = ∑ j, hA.eigenvalues j * ‖inner ℂ (hA.eigenvectorBasis j) x‖ ^ 2 := by
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hA
  have key : ∀ j, inner ℂ (hA.eigenvectorBasis j) ((Matrix.toEuclideanLin A) x)
      = (hA.eigenvalues j : ℂ) * inner ℂ (hA.eigenvectorBasis j) x := by
    intro j
    rw [← hsym, toEuclideanLin_eigenvectorBasis hA j, inner_smul_left]
    simp
  unfold quadForm
  rw [← (hA.eigenvectorBasis).sum_inner_mul_inner x ((Matrix.toEuclideanLin A) x), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, show (inner ℂ x (hA.eigenvectorBasis j) : ℂ)
      = starRingEnd ℂ (inner ℂ (hA.eigenvectorBasis j) x) from (inner_conj_symm _ _).symm,
    show (starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis j) x)
        * ((hA.eigenvalues j : ℂ) * inner ℂ (hA.eigenvectorBasis j) x)
      = (hA.eigenvalues j : ℂ) * ((starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis j) x)
        * inner ℂ (hA.eigenvectorBasis j) x) by ring, RCLike.conj_mul]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]

