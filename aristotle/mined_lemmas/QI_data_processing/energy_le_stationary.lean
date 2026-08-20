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

theorem energy_le_stationary (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    (hX₀ : σ * X₀ + (t : ℂ) • (X₀ * ρ) = ρ) (X : Matrix n n ℂ) :
    energy ρ σ t X ≤ energy ρ σ t X₀ := by
  have := energy_add hρ.isHermitian hσ.isHermitian hX₀ (X - X₀)
  rw [add_sub_cancel] at this
  have h1 : 0 ≤ (Matrix.trace ((X - X₀)ᴴ * σ * (X - X₀))).re := by
    have : ((X - X₀)ᴴ * σ * (X - X₀)).PosSemidef := hσ.conjTranspose_mul_mul_same _
    exact (Complex.le_def.mp this.trace_nonneg).1
  have h2 : 0 ≤ (Matrix.trace ((X - X₀)ᴴ * (X - X₀) * ρ)).re := by
    have hpsd : ((X - X₀)ᴴ * (X - X₀)).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
    exact trace_mul_re_nonneg hpsd hρ
  nlinarith [mul_nonneg ht h2]

