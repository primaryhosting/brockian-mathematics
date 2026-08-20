/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix `A`: the number of indices `i` at which
the eigenvalue function `hA.eigenvalues` is strictly positive (i.e. the number of strictly
positive eigenvalues of `A`, counted with multiplicity). -/

theorem re_star_dotProduct_mulVec_eq_sum (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re
      = ∑ i, hA.eigenvalues i *
          ‖(inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) : ℂ)‖ ^ 2 := by
  have hsym : (Matrix.toLpLin 2 2 A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hT : ∀ i, (Matrix.toLpLin 2 2 A) (hA.eigenvectorBasis i)
      = (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    intro i
    apply WithLp.ofLp_injective (p := 2)
    show A *ᵥ (WithLp.ofLp (hA.eigenvectorBasis i)) = _
    rw [hA.mulVec_eigenvectorBasis i]
    simp
  have h1 : (star x ⬝ᵥ A *ᵥ x)
      = inner ℂ (WithLp.toLp 2 x) ((Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x)) := by
    rw [show (Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ x) from rfl,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have h3 : (inner ℂ (WithLp.toLp 2 x) ((Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x)) : ℂ)
      = ∑ i, (hA.eigenvalues i : ℂ) *
          ((‖(inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x)
      ((Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsym (hA.eigenvectorBasis i) (WithLp.toLp 2 x), hT i, inner_smul_left,
      Complex.conj_ofReal]
    have hc : (inner ℂ (WithLp.toLp 2 x) (hA.eigenvectorBasis i) : ℂ)
        = starRingEnd ℂ (inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x)) :=
      (inner_conj_symm _ _).symm
    rw [hc]
    set z : ℂ := inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x)
    have h : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; norm_cast
    calc (starRingEnd ℂ) z * ((hA.eigenvalues i : ℂ) * z)
        = (hA.eigenvalues i : ℂ) * ((starRingEnd ℂ) z * z) := by ring
      _ = _ := by rw [h]
  rw [h1, h3, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- The linear map sending a vector to its coordinates, in the eigenbasis of the Hermitian
matrix `A`, along the eigenvectors with strictly positive eigenvalue. -/
