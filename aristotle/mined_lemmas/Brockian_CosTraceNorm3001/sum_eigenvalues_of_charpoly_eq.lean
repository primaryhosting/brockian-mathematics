import Mathlib

/-!
# Trace-norm bounds for the cosine of a Hermitian matrix (`CosTraceNorm` family)

For a complex `n × n` matrix `B` the *trace norm* (Schatten 1-norm) is the sum of the singular
values of `B`, i.e. the sum of the square roots of the eigenvalues of the positive semidefinite
matrix `Bᴴ * B`.  This file introduces that notion (`Brockian.traceNorm`), identifies it with
`∑ i, |eigenvalue i|` for Hermitian matrices, and proves a family of bounds for the matrix
`cos A := cfc Real.cos A` obtained from a Hermitian matrix `A` by the continuous functional
calculus.
-/

open scoped BigOperators
open Matrix Polynomial

namespace Brockian

variable {n : ℕ}

/-- The trace norm (Schatten 1-norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Bᴴ * B`. -/

theorem sum_eigenvalues_of_charpoly_eq {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian)
    (d : Fin n → ℝ) (hd : B.charpoly = ∏ i, (X - C ((d i : ℂ)))) (g : ℝ → ℝ) :
    ∑ i, g (hB.eigenvalues i) = ∑ i, g (d i) := by
  have h1 : B.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hB.eigenvalues) Finset.univ.val :=
    hB.roots_charpoly_eq_eigenvalues
  have h2 : B.charpoly.roots = Multiset.map (fun i => ((d i : ℂ))) Finset.univ.val := by
    rw [hd, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h3 := h1.symm.trans h2
  have h4 := congrArg (Multiset.map (fun z : ℂ => g (RCLike.re z))) h3
  simp only [Multiset.map_map, Function.comp_def, RCLike.ofReal_re] at h4
  have h5 := congrArg Multiset.sum h4
  simpa [Finset.sum, Function.comp_def] using h5

/-- For a Hermitian matrix `B`, the matrix `Bᴴ * B` has characteristic polynomial with roots the
squares of the eigenvalues of `B`. -/
