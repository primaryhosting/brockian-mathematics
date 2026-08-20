import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

theorem quadForm_resolvent {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 ≤ hA.eigenvalues k) {t : ℝ} (ht : 0 < t) (x : n → ℂ) :
    star x ⬝ᵥ ((A + (t : ℂ) • 1)⁻¹ *ᵥ x)
      = ∑ k, (((hA.eigenvalues k + t)⁻¹ * specCoeff hA x k : ℝ) : ℂ) := by
  rw [resolvent_decomp hA hpos ht, quadForm_conj_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, specCoeff, Complex.normSq_eq_conj_mul_self]

