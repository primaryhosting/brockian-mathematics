import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Matrix

open NormedSpace (exp)

/-!
# Trace-norm bounds for matrix trigonometric functions

For an `n × n` complex matrix `A` we define the matrix cosine and matrix sine through the
matrix exponential,
`cos A = (exp (i A) + exp (-i A)) / 2` and `sin A = (exp (i A) - exp (-i A)) / (2 i)`.

The main results (`CosTraceNorm2707` and friends) bound the absolute value of the trace of these
matrices by the size `n` of the matrix, whenever `A` is Hermitian.  The proof goes through the
observation that `exp (± i A)` is unitary for Hermitian `A`, so that all of its entries have
absolute value at most `1`.
-/

namespace Brockian

variable {n : ℕ}

/-- The matrix cosine of a square complex matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/

lemma norm_entry_le_one_of_conjTranspose_mul {U : Matrix (Fin n) (Fin n) ℂ}
    (h : Uᴴ * U = 1) (i j : Fin n) : ‖U i j‖ ≤ 1 := by
  have h1 : (Uᴴ * U) j j = 1 := by rw [h]; simp
  rw [Matrix.mul_apply] at h1
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul] at h1
  have h2 : ((∑ k, ‖U k j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h1
  have h2' : ∑ k, ‖U k j‖ ^ 2 = (1 : ℝ) := Complex.ofReal_inj.mp h2
  have h3 : ‖U i j‖ ^ 2 ≤ 1 := by
    rw [← h2']
    exact Finset.single_le_sum (f := fun k => ‖U k j‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (U i j)]

/-- A matrix all of whose entries have norm at most `1` has trace of norm at most `n`. -/
