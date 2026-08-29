/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped ComplexOrder

namespace Brockian

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `i`-th singular value of a complex square matrix `A`: the square root of the `i`-th
eigenvalue of the positive semidefinite matrix `Aᴴ * A`. -/

lemma sum_singularValue_sq (A : Matrix n n ℂ) :
    ∑ i, singularValue A i ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := (isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues
  rw [trace_conjTranspose_mul_self A] at h
  have h' : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i, (isHermitian_conjTranspose_mul_self A).eigenvalues i : ℝ) : ℂ) := by
    rw [h]; push_cast; rfl
  have h'' : (∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) =
      ∑ i, (isHermitian_conjTranspose_mul_self A).eigenvalues i := by
    exact_mod_cast h'
  simp only [singularValue_sq]
  exact h''.symm

/-- **Frobenius vs. trace norm.**  The Frobenius (Hilbert-Schmidt) norm of a matrix is at most
its trace norm. -/
