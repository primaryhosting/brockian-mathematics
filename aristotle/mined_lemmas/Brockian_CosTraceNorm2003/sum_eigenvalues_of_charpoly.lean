import Mathlib

/-!
# Trace-norm bounds for the matrix cosine and sine (`CosTraceNorm` family)

This file develops, from scratch, the Schatten 1-norm (trace norm) of a complex square matrix,
the Hermitian functional calculus `Brockian.hermFun`, and proves a family of trace-norm bounds
for the matrix cosine and sine of a Hermitian matrix.
-/

set_option maxRecDepth 8000

open scoped BigOperators
open Matrix Polynomial

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a complex square matrix: the sum of its singular
values, i.e. the sum of the square roots of the eigenvalues of `Aᴴ * A`. -/

lemma sum_eigenvalues_of_charpoly {A : Matrix n n ℂ} (hA : A.IsHermitian) (μ : n → ℝ)
    (h : A.charpoly = ∏ i, (X - C ((μ i : ℝ) : ℂ))) (f : ℝ → ℝ) :
    ∑ i, f (hA.eigenvalues i) = ∑ i, f (μ i) := by
  have hroots : A.charpoly.roots = Multiset.map (fun i => ((μ i : ℝ) : ℂ)) Finset.univ.val := by
    rw [h, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h2 := hA.roots_charpoly_eq_eigenvalues
  rw [hroots] at h2
  have h3 : Multiset.map (fun i => hA.eigenvalues i) Finset.univ.val
      = Multiset.map (fun i => μ i) Finset.univ.val := by
    have := congrArg (Multiset.map Complex.re) h2.symm
    simpa [Multiset.map_map, Function.comp_def] using this
  have h4 := congrArg (fun m => (Multiset.map f m).sum) h3
  simp only [Multiset.map_map, Function.comp_def] at h4
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact h4

/-- Conjugating a real diagonal matrix by a unitary does not change the characteristic
polynomial. -/
