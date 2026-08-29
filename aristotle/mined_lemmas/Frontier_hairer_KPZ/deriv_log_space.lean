/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- `IsSHESolution ξ Z` says that the (smooth, strictly positive) function `Z : ℝ → ℝ → ℝ`,
written `Z t x`, is a classical solution of the multiplicative stochastic heat equation
`∂_t Z = ∂_x² Z + Z ξ` driven by the (function-valued) noise `ξ`. -/
structure IsSHESolution (xi Z : ℝ → ℝ → ℝ) : Prop where
  /-- `Z` is strictly positive. -/
  pos : ∀ t x, 0 < Z t x
  /-- `Z` is differentiable in time. -/
  diff_time : ∀ x, Differentiable ℝ fun t => Z t x
  /-- `Z` is differentiable in space. -/
  diff_space : ∀ t, Differentiable ℝ fun x => Z t x
  /-- The spatial derivative of `Z` is again differentiable in space. -/
  diff_space₂ : ∀ t, Differentiable ℝ fun x => deriv (fun y => Z t y) x
  /-- The equation `∂_t Z = ∂_x² Z + Z ξ`. -/
  eqn : ∀ t x,
    deriv (fun s => Z s x) t = deriv (deriv fun y => Z t y) x + Z t x * xi t x

/-- `IsKPZSolution ξ h` says that the (smooth) function `h : ℝ → ℝ → ℝ`, written `h t x`, is a
classical solution of the KPZ equation `∂_t h = ∂_x² h + (∂_x h)² + ξ` driven by `ξ`. -/
structure IsKPZSolution (xi h : ℝ → ℝ → ℝ) : Prop where
  /-- `h` is differentiable in time. -/
  diff_time : ∀ x, Differentiable ℝ fun t => h t x
  /-- `h` is differentiable in space. -/
  diff_space : ∀ t, Differentiable ℝ fun x => h t x
  /-- The spatial derivative of `h` is again differentiable in space. -/
  diff_space₂ : ∀ t, Differentiable ℝ fun x => deriv (fun y => h t y) x
  /-- The equation `∂_t h = ∂_x² h + (∂_x h)² + ξ`. -/
  eqn : ∀ t x,
    deriv (fun s => h s x) t =
      deriv (deriv fun y => h t y) x + (deriv (fun y => h t y) x) ^ 2 + xi t x

section ColeHopf

variable {xi Z h : ℝ → ℝ → ℝ}

/-- First spatial derivative of `log Z`. -/

lemma deriv_log_space (hZpos : ∀ t x, 0 < Z t x)
    (hZx : ∀ t, Differentiable ℝ fun x => Z t x) (t : ℝ) :
    (deriv fun y => Real.log (Z t y)) = fun y => deriv (fun z => Z t z) y / Z t y := by
  funext y
  exact (((hZx t y).hasDerivAt).log (hZpos t y).ne').deriv

/-- First spatial derivative of `exp h`. -/
