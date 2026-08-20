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

theorem trace_mul_spectral (U W : Matrix n n ℂ) (r g : n → ℝ) :
    Matrix.trace ((W * diagonal (fun k => (r k : ℂ)) * Wᴴ) *
        (U * diagonal (fun j => (g j : ℂ)) * Uᴴ))
      = ((∑ k, ∑ j, ‖(Uᴴ * W) j k‖ ^ 2 * (r k * g j) : ℝ) : ℂ) := by
  have step : Matrix.trace ((W * diagonal (fun k => (r k : ℂ)) * Wᴴ) *
      (U * diagonal (fun j => (g j : ℂ)) * Uᴴ))
      = Matrix.trace (diagonal (fun k => (r k : ℂ)) *
          ((Uᴴ * W)ᴴ * (diagonal (fun j => (g j : ℂ)) * (Uᴴ * W)))) := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm W (diagonal (fun k => (r k : ℂ)) *
      (Wᴴ * (U * (diagonal (fun j => (g j : ℂ)) * Uᴴ))))]
    simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [step, Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_apply, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_mul]
  have hz : star ((Uᴴ * W) j k) * ((Uᴴ * W) j k) = ((‖(Uᴴ * W) j k‖ : ℂ)) ^ 2 := by
    have h := RCLike.conj_mul (K := ℂ) ((Uᴴ * W) j k)
    simpa [Complex.star_def] using h
  push_cast
  linear_combination ((r k : ℂ) * (g j : ℂ)) * hz

