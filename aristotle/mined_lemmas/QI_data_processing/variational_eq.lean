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

theorem variational_eq {S : Matrix N N ℂ} (hS : S.PosDef) (xi : N → ℂ) :
    2 * (star (S⁻¹ *ᵥ xi) ⬝ᵥ xi).re - (star (S⁻¹ *ᵥ xi) ⬝ᵥ (S *ᵥ (S⁻¹ *ᵥ xi))).re
      = (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
  have hSy : S *ᵥ (S⁻¹ *ᵥ xi) = xi := by
    rw [Matrix.mulVec_mulVec, posDef_mul_inv hS, Matrix.one_mulVec]
  have h2 : (star (S⁻¹ *ᵥ xi) ⬝ᵥ xi).re = (star xi ⬝ᵥ (S⁻¹ *ᵥ xi)).re := by
    rw [star_dotProduct]; simp
  rw [hSy, h2]
  ring

end QI

import Mathlib

/-!
# Spectral tools for Hermitian matrices

Functional calculus for Hermitian complex matrices computed through an arbitrary
unitary diagonalization, quadratic forms, and the integral representation of the
logarithm.
-/

open Matrix Filter MeasureTheory
open scoped ComplexOrder
open scoped BigOperators Topology

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal embedding of `n → ℂ` into matrices, as a star algebra homomorphism. -/
