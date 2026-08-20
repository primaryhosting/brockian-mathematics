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

theorem stationary_of_spectral {ρ σ : Matrix n n ℂ} {t : ℝ} (U W : Matrix n n ℂ) (r s : n → ℝ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (hW : Wᴴ * W = 1)
    (hσe : σ = U * diagonal (fun j => (s j : ℂ)) * Uᴴ)
    (hρe : ρ = W * diagonal (fun k => (r k : ℂ)) * Wᴴ)
    (hne : ∀ j k, s j + t * r k ≠ 0) :
    σ * (U * sylvesterCoeff r s t (Uᴴ * W) * Wᴴ)
      + (t : ℂ) • (U * sylvesterCoeff r s t (Uᴴ * W) * Wᴴ * ρ) = ρ := by
  set D := sylvesterCoeff r s t (Uᴴ * W) with hD
  set S : Matrix n n ℂ := diagonal (fun j => (s j : ℂ)) with hS
  set R : Matrix n n ℂ := diagonal (fun k => (r k : ℂ)) with hR
  have h1 : σ * (U * D * Wᴴ) = U * (S * D) * Wᴴ := by
    rw [hσe]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have h2 : U * D * Wᴴ * ρ = U * (D * R) * Wᴴ := by
    rw [hρe]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
  have h3 : U * ((Uᴴ * W) * R) * Wᴴ = ρ := by
    rw [hρe]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul]
  have h4 : (t : ℂ) • (U * (D * R) * Wᴴ) = U * ((t : ℂ) • (D * R)) * Wᴴ := by
    simp
  rw [h1, h2, h4, ← Matrix.add_mul, ← Matrix.mul_add, hD, sylvester_solve r s t (Uᴴ * W) hne, h3]


