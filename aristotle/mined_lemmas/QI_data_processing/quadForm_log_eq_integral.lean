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

theorem quadForm_log_eq_integral {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 < hA.eigenvalues k) (x : n → ℂ) :
    (star x ⬝ᵥ ((cfc Real.log A) *ᵥ x)).re
      = ∫ t in Set.Ioi (0:ℝ), resolvIntegrand A x t := by
  have hcongr : ∫ t in Set.Ioi (0:ℝ), resolvIntegrand A x t
      = ∫ t in Set.Ioi (0:ℝ), ∑ k, specCoeff hA x k * (1/(1+t) - 1/(hA.eigenvalues k + t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact resolvIntegrand_eq hA (fun k => (hpos k).le) ht x
  rw [hcongr, MeasureTheory.integral_finset_sum]
  · rw [quadForm_cfc hA Real.log x]
    simp only [Complex.re_sum, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MeasureTheory.integral_const_mul, (logRepr (hpos k)).2]
    ring
  · intro k _
    exact ((logRepr (hpos k)).1).smul (specCoeff hA x k)

end QI

import RequestProject.Spectral

/-!
# Logarithms of Kronecker products, inverses and transposes
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Existence of a unitary diagonalization with real eigenvalues. -/
