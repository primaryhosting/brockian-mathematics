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

lemma resolvIntegrand_eq {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 ≤ hA.eigenvalues k) {t : ℝ} (ht : 0 < t) (x : n → ℂ) :
    resolvIntegrand A x t
      = ∑ k, specCoeff hA x k * (1/(1+t) - 1/(hA.eigenvalues k + t)) := by
  rw [resolvIntegrand, quadForm_self hA x, quadForm_resolvent hA hpos ht x]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div, one_div]
  ring

