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

namespace Brockian

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix cosine of a complex square matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/

lemma trace_cosMat_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (cosMat A).trace = ∑ i, (Real.cos (hA.eigenvalues i) : ℂ) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary.2
  have hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have h := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have key : ∀ z : ℂ, (exp (z • A)).trace = ∑ i, Complex.exp (z * (hA.eigenvalues i : ℂ)) := by
    intro z
    have hsm : z • A = U * Matrix.diagonal (fun i => z * (hA.eigenvalues i : ℂ)) * star U := by
      have hd : (Matrix.diagonal (fun i => z * (hA.eigenvalues i : ℂ)))
          = z • Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
        rw [← Matrix.diagonal_smul]; rfl
      rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← hspec]
    rw [hsm, exp_conj_unitary hU, trace_conj_unitary hU, exp_diagonal_complex,
      Matrix.trace_diagonal]
  have h1 := key Complex.I
  have h2 := key (-Complex.I)
  have hneg : -(Complex.I • A) = (-Complex.I) • A := by module
  rw [cosMat, Matrix.trace_smul, Matrix.trace_add, hneg, h1, h2, ← Finset.sum_add_distrib,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Complex.exp (Complex.I * (hA.eigenvalues i : ℂ))
      + Complex.exp (-Complex.I * (hA.eigenvalues i : ℂ))
      = 2 * Complex.cos (hA.eigenvalues i : ℂ) := by
    rw [Complex.cos]; ring_nf
  rw [hc, ← Complex.ofReal_cos]
  ring

/-- The trace of `A * A` for Hermitian `A` is the sum of the squares of the eigenvalues. -/
