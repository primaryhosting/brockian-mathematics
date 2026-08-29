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

/-
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp` turns sums of commuting elements into products (specialization of
`NormedSpace.exp_add_of_commute_of_mem_ball` to a real Banach algebra). -/

theorem exp_add_comm {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball h ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

