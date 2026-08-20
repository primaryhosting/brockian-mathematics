import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.QI.KadisonSchwarz

/-!
# A variational formula for the resolvent quantity `G`

For positive semidefinite `ρ`, `σ` and `t ≥ 0` we consider the concave functional

`energy ρ σ t X = 2 Re Tr (ρ X) - Re Tr (Xᴴ σ X) - t Re Tr (Xᴴ X ρ)`

and its supremum `Gfun ρ σ t`.  This is a variational form of
`⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫` for the relative modular operator `Δ : Z ↦ σ Z ρ⁻¹`.

Two facts are proved here:

* `Gfun` is computed by any stationary point (`Gfun_eq_of_stationary`), and a stationary
  point exists whenever `σ` is positive definite, with an explicit spectral value
  (`Gfun_spectral`);
* `Gfun` is monotone under quantum channels (`Gfun_krausMap_le`).
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- The concave functional whose supremum is `Gfun`. -/

theorem energy_add (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) (Z : Matrix n n ℂ) :
    energy ρ σ t (X₀ + Z) =
      energy ρ σ t X₀ -
        ((Matrix.trace (Zᴴ * σ * Z)).re + t * (Matrix.trace (Zᴴ * Z * ρ)).re) := by
  have hcross1 : (Matrix.trace (Zᴴ * σ * X₀)).re = (Matrix.trace (X₀ᴴ * σ * Z)).re := by
    have h : (X₀ᴴ * σ * Z)ᴴ = Zᴴ * σ * X₀ := by
      simp [Matrix.conjTranspose_mul, hσ.eq, Matrix.mul_assoc]
    rw [← h, Matrix.trace_conjTranspose]
    simp
  have hcross2 : (Matrix.trace (Zᴴ * X₀ * ρ)).re = (Matrix.trace (X₀ᴴ * Z * ρ)).re := by
    have h : (X₀ᴴ * Z * ρ)ᴴ = ρ * Zᴴ * X₀ := by
      simp [Matrix.conjTranspose_mul, hρ.eq, Matrix.mul_assoc]
    have h2 : Matrix.trace (ρ * Zᴴ * X₀) = Matrix.trace (Zᴴ * X₀ * ρ) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [← h2, ← h, Matrix.trace_conjTranspose]
    simp
  have hA : Matrix.trace (ρ * (X₀ + Z)) = Matrix.trace (ρ * X₀) + Matrix.trace (ρ * Z) := by
    rw [Matrix.mul_add, Matrix.trace_add]
  have hB : Matrix.trace ((X₀ + Z)ᴴ * σ * (X₀ + Z)) =
      Matrix.trace (X₀ᴴ * σ * X₀) + Matrix.trace (X₀ᴴ * σ * Z) + Matrix.trace (Zᴴ * σ * X₀)
        + Matrix.trace (Zᴴ * σ * Z) := by
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    ring
  have hC : Matrix.trace ((X₀ + Z)ᴴ * (X₀ + Z) * ρ) =
      Matrix.trace (X₀ᴴ * X₀ * ρ) + Matrix.trace (X₀ᴴ * Z * ρ) + Matrix.trace (Zᴴ * X₀ * ρ)
        + Matrix.trace (Zᴴ * Z * ρ) := by
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    ring
  have hst := trace_stationary_re hρ hσ hX₀ Z
  simp only [energy, hA, hB, hC, Complex.add_re]
  linear_combination (-2 : ℝ) * hst - hcross1 - t * hcross2

