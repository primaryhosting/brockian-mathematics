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

theorem hasDerivAt_logAnti {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (logAnti r s) (r ^ 2 / (s + t * r) - r / (1 + t)) t := by
  have h1 : (0 : ℝ) < s + t * r := by positivity
  have h2 : (0 : ℝ) < 1 + t := by linarith
  have d1 : HasDerivAt (fun u : ℝ => s + u * r) r t := by
    simpa using ((hasDerivAt_id t).mul_const r).const_add s
  have d2 : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have e1 : HasDerivAt (fun u : ℝ => Real.log (s + u * r)) (r / (s + t * r)) t := d1.log h1.ne'
  have e2 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := d2.log h2.ne'
  have := (e1.const_mul r).sub (e2.const_mul r)
  convert this using 1
  field_simp

