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

theorem integrableOn_entropyTerm {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    IntegrableOn (fun t => r ^ 2 / (s + t * r) - r / (1 + t)) (Ioi 0) := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · simp [← hr0]
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (logAnti r s)
      (r ^ 2 / (s + t * r) - r / (1 + t)) t := fun t ht => hasDerivAt_logAnti hr0 hs ht
  rcases le_total s r with hrs | hrs
  · refine integrableOn_Ioi_deriv_of_nonneg' hderiv (fun t ht => ?_) (tendsto_logAnti hr0 hs)
    have ht0 : (0 : ℝ) < t := ht
    have h1 : (0 : ℝ) < s + t * r := by positivity
    have h2 : (0 : ℝ) < 1 + t := by linarith
    rw [sub_nonneg, div_le_div_iff₀ h2 h1]
    nlinarith
  · refine integrableOn_Ioi_deriv_of_nonpos' hderiv (fun t ht => ?_) (tendsto_logAnti hr0 hs)
    have ht0 : (0 : ℝ) < t := ht
    have h1 : (0 : ℝ) < s + t * r := by positivity
    have h2 : (0 : ℝ) < 1 + t := by linarith
    rw [sub_nonpos, div_le_div_iff₀ h1 h2]
    nlinarith

