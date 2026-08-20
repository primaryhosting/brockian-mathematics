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

lemma integrableOn_resolvIntegrand {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 < hA.eigenvalues k) (x : n → ℂ) :
    IntegrableOn (resolvIntegrand A x) (Set.Ioi 0) := by
  have hsum : IntegrableOn
      (fun t => ∑ k, specCoeff hA x k * (1/(1+t) - 1/(hA.eigenvalues k + t))) (Set.Ioi 0) := by
    apply MeasureTheory.integrable_finset_sum
    intro k _
    exact ((logRepr (hpos k)).1).smul (specCoeff hA x k)
  exact hsum.congr_fun (fun t ht => (resolvIntegrand_eq hA (fun k => (hpos k).le) ht x).symm)
    measurableSet_Ioi

/-- **Integral representation of the quadratic form of the matrix logarithm.** -/
