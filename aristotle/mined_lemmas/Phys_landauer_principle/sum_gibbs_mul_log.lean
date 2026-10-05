import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma sum_gibbs_mul_log :
    ∑ b : B, gibbs beta E b * Real.log (gibbs beta E b)
      = -beta * (∑ b : B, gibbs beta E b * E b)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) := by
  have step : ∀ b : B, gibbs beta E b * Real.log (gibbs beta E b)
      = -beta * (gibbs beta E b * E b)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) * gibbs beta E b := by
    intro b
    rw [log_gibbs]
    ring
  rw [Finset.sum_congr rfl fun b _ => step b, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, gibbs_sum, mul_one]

include hp1 in
