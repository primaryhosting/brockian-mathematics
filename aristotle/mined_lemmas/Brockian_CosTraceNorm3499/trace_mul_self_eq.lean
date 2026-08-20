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

lemma trace_mul_self_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : U ∈ Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary.2
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hspec : A = U * D * star U := by
    have h := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hAA : A * A = U * (D * D) * star U := by
    conv_lhs => rw [hspec]
    have h2 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
    calc U * D * star U * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * (D * D) * star U := by rw [h2]; noncomm_ring
  rw [hAA, trace_conj_unitary hU, hDdef, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [Function.comp, sq]

/-- **Second-order trace-norm bound for the matrix cosine.**  For a Hermitian complex `n × n`
matrix `A`, the trace of `cos A` differs from `n` by at most `Tr (A²) / 2`. -/
