import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open NormedSpace

/-- In a complex Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem exp_add_of_commute_complex {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜]
    [CompleteSpace 𝒜] {x y : 𝒜} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball h ((expSeries_radius_eq_top ℂ 𝒜).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℂ 𝒜).symm ▸ edist_lt_top _ _)

/-- In a Banach algebra, `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1`. -/
