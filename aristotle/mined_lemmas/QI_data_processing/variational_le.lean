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

theorem variational_le {S : Matrix N N ℂ} (hS : S.PosDef) (xi x : N → ℂ) :
    2 * (star x ⬝ᵥ xi).re - (star x ⬝ᵥ (S *ᵥ x)).re
      ≤ (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
  set y := S⁻¹ *ᵥ xi with hy
  have hSy : S *ᵥ y = xi := by
    rw [hy, Matrix.mulVec_mulVec, posDef_mul_inv hS, Matrix.one_mulVec]
  have h0 : (0:ℝ) ≤ (star (x - y) ⬝ᵥ (S *ᵥ (x - y))).re := by
    have := hS.posSemidef.dotProduct_mulVec_nonneg (x - y)
    exact_mod_cast Complex.le_def.mp this |>.1
  rw [quad_expand S x y, hSy] at h0
  have h1 : (star y ⬝ᵥ (S *ᵥ x)).re = (star x ⬝ᵥ xi).re := by
    rw [dot_herm_symm hS.isHermitian y x, hSy]
    simp
  have h2 : (star y ⬝ᵥ xi).re = (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
    rw [hy, star_dotProduct]
    simp
  simp only [Complex.sub_re, Complex.add_re] at h0
  rw [h1, h2] at h0
  linarith

/-- The bound in `variational_le` is attained at `x = S⁻¹ ξ`. -/
