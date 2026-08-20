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

theorem kadison_schwarz_isometry {p : Type*} [Fintype p] [DecidableEq p]
    (R : Matrix p n ℂ) (hR : Rᴴ * R = 1) (Y : Matrix p p ℂ) :
    ((Rᴴ * (Yᴴ * Y) * R) - (Rᴴ * Y * R)ᴴ * (Rᴴ * Y * R)).PosSemidef := by
  have hP : ((1 : Matrix p p ℂ) - R * Rᴴ).PosSemidef := by
    have hid : ((1 : Matrix p p ℂ) - R * Rᴴ)ᴴ * ((1 : Matrix p p ℂ) - R * Rᴴ)
        = (1 : Matrix p p ℂ) - R * Rᴴ := by
      have : (R * Rᴴ) * (R * Rᴴ) = R * Rᴴ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R Rᴴ, hR, Matrix.one_mul]
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, this]
      abel
    rw [← hid]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have key : (Rᴴ * (Yᴴ * Y) * R) - (Rᴴ * Y * R)ᴴ * (Rᴴ * Y * R)
      = (Y * R)ᴴ * ((1 : Matrix p p ℂ) - R * Rᴴ) * (Y * R) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [key]
  exact hP.conjTranspose_mul_mul_same _

/-- The stacked Kraus operators, an isometry when the channel is trace preserving. -/
