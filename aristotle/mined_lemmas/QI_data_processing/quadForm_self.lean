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

theorem quadForm_self {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ x = ∑ k, ((specCoeff hA x k : ℝ) : ℂ) := by
  have h1 : ((hA.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (fun _ : n => (1 : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ = 1 := by
    rw [show diagonal (fun _ : n => (1 : ℂ)) = 1 from by simp, Matrix.mul_one, eigen_unitary hA]
  have h2 := quadForm_conj_diagonal (hA.eigenvectorUnitary : Matrix n n ℂ) (fun _ => (1:ℂ)) x
  rw [h1] at h2
  simp only [Matrix.one_mulVec, one_mul] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [specCoeff, Complex.normSq_eq_conj_mul_self]

/-- Integral representation of the real logarithm:
`log l = ∫_0^∞ (1/(1+t) - 1/(l+t)) dt`, together with integrability of the integrand. -/
