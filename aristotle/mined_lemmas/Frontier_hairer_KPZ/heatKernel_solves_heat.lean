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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Space-time partial derivatives

We work with real functions `f : ℝ → ℝ → ℝ` of a time variable and a (one dimensional)
space variable. -/

/-- Partial derivative in the time variable. -/

theorem heatKernel_solves_heat {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dt heatKernel t x = dx (dx heatKernel) t x := by
  rw [dt_heatKernel ht, dx_dx_heatKernel ht]

/-! ## Main statement -/

/-- **Hairer's KPZ equation, Cole–Hopf reduction and base case.**

The KPZ equation `∂_t h = ∂_x² h + (∂_x h)² + ξ` is, at the level of classical solutions,
equivalent via the Cole–Hopf transform `h = log Z`, `Z = exp h` to the *linear* multiplicative
stochastic heat equation `∂_t Z = ∂_x² Z + Z ξ`: the transform is a regularity-preserving
bijection between positive solutions of the latter and solutions of the former.  This is the
deterministic backbone of Hairer's solution theory for KPZ.  In addition the equation is
solvable in the base case of a spatially homogeneous continuous noise, and the Gaussian heat
kernel is a positive classical solution of the linear equation `∂_t Z = ∂_x² Z` for `t > 0`. -/
