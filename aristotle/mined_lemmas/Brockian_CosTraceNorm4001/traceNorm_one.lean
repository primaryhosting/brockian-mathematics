import Mathlib

/-!
# A trace-norm bound for the matrix cosine

For a Hermitian complex matrix `A` we define the matrix cosine and sine by

  `cos A = (exp (I • A) + exp (-(I • A))) / 2`,  `sin A = (exp (I • A) - exp (-(I • A))) / (2 I)`,

and the trace norm (nuclear norm) of a matrix `M` as the sum of its singular values, i.e.
the sum of the square roots of the eigenvalues of `Mᴴ * M`.

The main result `Brockian.CosTraceNorm4001` states `‖cos A‖₁ ≤ card n`.
-/

namespace Brockian

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (nuclear norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Mᴴ * M`. -/

lemma traceNorm_one : traceNorm (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
  have h : ∀ i : n,
      (Matrix.isHermitian_conjTranspose_mul_self (1 : Matrix n n ℂ)).eigenvalues i = 1 := by
    intro i
    haveI : Nonempty n := ⟨i⟩
    have hmem :=
      (Matrix.isHermitian_conjTranspose_mul_self (1 : Matrix n n ℂ)).eigenvalues_mem_spectrum_real i
    have hspec : spectrum ℝ ((1 : Matrix n n ℂ)ᴴ * 1) = {1} := by
      rw [Matrix.conjTranspose_one, Matrix.one_mul]; exact spectrum.one_eq
    rw [hspec] at hmem
    simpa using hmem
  have h' : ∀ i : n,
      Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self (1 : Matrix n n ℂ)).eigenvalues i)
        = 1 := fun i => by rw [h i, Real.sqrt_one]
  rw [traceNorm, Finset.sum_congr rfl (fun i _ => h' i)]
  simp

