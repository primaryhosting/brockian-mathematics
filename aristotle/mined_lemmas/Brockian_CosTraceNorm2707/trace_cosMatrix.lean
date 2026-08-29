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

theorem trace_cosMatrix (hA : A.IsHermitian) :
    Matrix.trace (cosMatrix hA) = ∑ i, (Real.cos (hA.eigenvalues i) : ℂ) := by
  have hUU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    congrArg Subtype.val (Unitary.star_mul_self hA.eigenvectorUnitary)
  rw [cosMatrix_eq hA, Matrix.trace_mul_cycle, hUU, one_mul, Matrix.trace_diagonal]

/-- **Cos Trace Norm 2707.**  For a Hermitian matrix `A` of size `n`, the matrix `cos A`
obtained from the spectral theorem satisfies the trace-norm bound `‖cos A‖₁ ≤ n`, and the
absolute value of its trace is dominated by that trace norm.  Consequently `|tr (cos A)| ≤ n`. -/
