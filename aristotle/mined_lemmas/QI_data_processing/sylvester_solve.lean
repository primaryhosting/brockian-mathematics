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

theorem sylvester_solve (r s : n → ℝ) (t : ℝ) (C : Matrix n n ℂ)
    (h : ∀ j k, s j + t * r k ≠ 0) :
    diagonal (fun j => (s j : ℂ)) * sylvesterCoeff r s t C
      + (t : ℂ) • (sylvesterCoeff r s t C * diagonal (fun k => (r k : ℂ)))
      = C * diagonal (fun k => (r k : ℂ)) := by
  ext j k
  simp only [sylvesterCoeff, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.of_apply, smul_eq_mul]
  have hd : s j + t * r k ≠ 0 := h j k
  have hd' : r k * t + s j ≠ 0 := by rw [mul_comm, ← add_comm]; exact hd
  have hs : ((r k / (s j + t * r k)) * s j + t * ((r k / (s j + t * r k)) * r k)) = r k := by
    have e : (r k / (s j + t * r k)) * s j + t * ((r k / (s j + t * r k)) * r k)
        = (r k * (s j + t * r k)) / (s j + t * r k) := by
      field_simp
    rw [e, mul_div_assoc, div_self hd, mul_one]
  have hsC := congrArg (fun x : ℝ => (x : ℂ)) hs
  push_cast at hsC ⊢
  linear_combination C j k * hsC

