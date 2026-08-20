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

lemma cfc_log_inv {A : Matrix n n ℂ} (hA : A.PosDef) :
    cfc Real.log A⁻¹ = - cfc Real.log A := by
  obtain ⟨U, d, hU, hU', hdpos, hdec⟩ := exists_diagonalization_pos hA
  have hne : ∀ k, ((d k : ℝ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hdpos k).ne'
  have hinv : A⁻¹ = U * diagonal (fun k => (((d k)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    rw [hdec, conj_diagonal_inv hU hU' hne]
    congr 2
    funext k
    simp
  rw [cfc_of_diagonalization (unitary_of_mul hU hU') (fun k => (d k)⁻¹) hinv Real.log,
    cfc_of_diagonalization (unitary_of_mul hU hU') d hdec Real.log]
  have hfun : (fun k => ((Real.log ((d k)⁻¹) : ℝ) : ℂ))
      = (fun k => -((Real.log (d k) : ℝ) : ℂ)) := by
    funext k
    simp [Real.log_inv]
  rw [hfun, ← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]

/-- The functional calculus commutes with transposition of a Hermitian matrix. -/
