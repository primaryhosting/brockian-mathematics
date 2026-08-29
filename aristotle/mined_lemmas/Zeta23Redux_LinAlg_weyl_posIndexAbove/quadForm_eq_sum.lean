import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The Rayleigh quadratic form of a matrix `M` at a vector `x` of Euclidean space:
`Re ⟪x, M x⟫`. -/

lemma quadForm_eq_sum {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadForm M x = ∑ i, hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 := by
  have hsym : (Matrix.toEuclideanLin M).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hM
  have key : (inner ℂ x (Matrix.toEuclideanLin M x) : ℂ)
      = ∑ i, ((hM.eigenvalues i * ‖(inner ℂ (hM.eigenvectorBasis i) x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hM.eigenvectorBasis.sum_inner_mul_inner x (Matrix.toEuclideanLin M x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (inner ℂ (hM.eigenvectorBasis i) (Matrix.toEuclideanLin M x) : ℂ)
        = (hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x := by
      rw [← hsym, toEuclideanLin_eigenvectorBasis hM i, inner_smul_left]
      simp
    rw [h1, ← inner_conj_symm (𝕜 := ℂ) x (hM.eigenvectorBasis i)]
    push_cast
    rw [show (starRingEnd ℂ) (inner ℂ (hM.eigenvectorBasis i) x)
          * ((hM.eigenvalues i : ℂ) * inner ℂ (hM.eigenvectorBasis i) x)
        = (hM.eigenvalues i : ℂ)
          * ((starRingEnd ℂ) (inner ℂ (hM.eigenvectorBasis i) x)
            * inner ℂ (hM.eigenvectorBasis i) x) by ring, Complex.conj_mul']
  rw [quadForm, key, ← Complex.ofReal_sum]
  simp only [Complex.ofReal_re]

/-- Squared norm expansion in the eigenbasis. -/
