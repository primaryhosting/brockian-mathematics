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

theorem trace_spectral {ρ : Matrix n n ℂ} {t : ℝ} (U W : Matrix n n ℂ) (r s : n → ℝ)
    (hW : Wᴴ * W = 1)
    (hρe : ρ = W * diagonal (fun k => (r k : ℂ)) * Wᴴ) :
    Matrix.trace (ρ * (U * sylvesterCoeff r s t (Uᴴ * W) * Wᴴ))
      = ((∑ k, ∑ j, (r k) ^ 2 * ‖(Uᴴ * W) j k‖ ^ 2 / (s j + t * r k) : ℝ) : ℂ) := by
  set C := Uᴴ * W with hC
  set D := sylvesterCoeff r s t C with hD
  set R : Matrix n n ℂ := diagonal (fun k => (r k : ℂ)) with hR
  have hWU : Wᴴ * U = Cᴴ := by rw [hC]; simp [Matrix.conjTranspose_mul]
  have step1 : Matrix.trace (ρ * (U * D * Wᴴ)) = Matrix.trace (R * Cᴴ * D) := by
    rw [hρe]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm W (R * (Wᴴ * (U * (D * Wᴴ))))]
    simp only [Matrix.mul_assoc, hW, Matrix.mul_one]
    rw [← Matrix.mul_assoc Wᴴ U D, hWU]
  rw [step1]
  rw [Matrix.trace]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hR, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hD, sylvesterCoeff, Matrix.of_apply]
  have hz : star (C j k) * C j k = ((‖C j k‖ : ℂ)) ^ 2 := by
    have h := RCLike.conj_mul (K := ℂ) (C j k)
    simpa [Complex.star_def] using h
  push_cast
  linear_combination ((r k : ℂ) * ((r k : ℂ) / ((s j : ℂ) + (t : ℂ) * (r k : ℂ)))) * hz


/-- The stationary point of `energy ρ σ t`, written in the eigenbases of `σ` and `ρ`. -/
