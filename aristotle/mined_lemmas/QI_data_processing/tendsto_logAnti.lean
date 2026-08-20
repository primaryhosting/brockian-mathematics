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

theorem tendsto_logAnti {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (logAnti r s) atTop (𝓝 (r * Real.log r)) := by
  have hden : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have h0 : Tendsto (fun t : ℝ => (s - r) / (1 + t)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  have h1 : Tendsto (fun t : ℝ => r + (s - r) / (1 + t)) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add h0
  have h2 : Tendsto (fun t : ℝ => Real.log (r + (s - r) / (1 + t))) atTop (𝓝 (Real.log r)) :=
    (Real.continuousAt_log hr.ne').tendsto.comp h1
  have h3 : Tendsto (fun t : ℝ => r * Real.log (r + (s - r) / (1 + t))) atTop
      (𝓝 (r * Real.log r)) := h2.const_mul r
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h4 : (0 : ℝ) < s + t * r := by positivity
  have h5 : (0 : ℝ) < 1 + t := by linarith
  have h6 : r + (s - r) / (1 + t) = (s + t * r) / (1 + t) := by
    field_simp
    ring
  rw [h6, Real.log_div h4.ne' h5.ne', logAnti]
  ring

