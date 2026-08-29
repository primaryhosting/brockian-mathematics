import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

open Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- The matrix `cos A` for a Hermitian matrix `A`, defined through the spectral theorem
(`Matrix.IsHermitian.spectral_theorem`): conjugate the diagonal matrix of the cosines of the
eigenvalues of `A` by the unitary matrix of eigenvectors of `A`. -/
noncomputable def cosMatrix (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ)) hA.eigenvectorUnitary
    (diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)))

/-- The trace norm (Schatten 1-norm) of `cos A`: since `cos A` is Hermitian with eigenvalues
`cos λᵢ`, its singular values are `|cos λᵢ|`. -/
noncomputable def cosTraceNorm (hA : A.IsHermitian) : ℝ :=
  ∑ i, |Real.cos (hA.eigenvalues i)|

private theorem star_diagonal_cos (hA : A.IsHermitian) :
    star (diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)))
      = diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp only [Matrix.diagonal_eq_diagonal_iff, Function.comp_apply, RCLike.star_def]
  exact fun i => by rw [← Complex.ofReal_cos, Complex.conj_ofReal]

/-- `cos A` is again Hermitian. -/
theorem cosMatrix_isHermitian (hA : A.IsHermitian) : (cosMatrix hA).IsHermitian := by
  rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, cosMatrix, ← map_star,
    star_diagonal_cos hA]

/-- Unfolded form of `cosMatrix`: it is the conjugation `U * diag(cos λ) * U*`. -/
theorem cosMatrix_eq (hA : A.IsHermitian) :
    cosMatrix hA = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * (diagonal (fun i => (Real.cos (hA.eigenvalues i) : ℂ)))
      * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
  Unitary.conjStarAlgAut_apply _ _

/-- The trace of `cos A` is the sum of the cosines of the eigenvalues of `A`. -/
theorem trace_cosMatrix (hA : A.IsHermitian) :
    Matrix.trace (cosMatrix hA) = ∑ i, (Real.cos (hA.eigenvalues i) : ℂ) := by
  have hUU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    congrArg Subtype.val (Unitary.star_mul_self hA.eigenvectorUnitary)
  rw [cosMatrix_eq hA, Matrix.trace_mul_cycle, hUU, one_mul, Matrix.trace_diagonal]

/-- **Cos Trace Norm 2707.**  For a Hermitian matrix `A` of size `n`, the matrix `cos A`
obtained from the spectral theorem satisfies the trace-norm bound `‖cos A‖₁ ≤ n`, and the
absolute value of its trace is dominated by that trace norm.  Consequently `|tr (cos A)| ≤ n`. -/
theorem CosTraceNorm2707 (hA : A.IsHermitian) :
    ‖Matrix.trace (cosMatrix hA)‖ ≤ cosTraceNorm hA ∧
      cosTraceNorm hA ≤ (n : ℝ) ∧
        ‖Matrix.trace (cosMatrix hA)‖ ≤ (n : ℝ) := by
  have h1 : ‖Matrix.trace (cosMatrix hA)‖ ≤ cosTraceNorm hA := by
    rw [trace_cosMatrix hA]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : cosTraceNorm hA ≤ (n : ℝ) := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), |Real.cos (hA.eigenvalues i)| ≤ 1 :=
      fun i _ => Real.abs_cos_le_one _
    calc cosTraceNorm hA ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum hle
      _ = (n : ℝ) := by simp
  exact ⟨h1, h2, h1.trans h2⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

