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

lemma sum_finalJoint_mul_log_gibbs :
    ∑ x : M × B, finalJoint beta E p U x * Real.log (gibbs beta E x.2)
      = -beta * (∑ x : M × B, finalJoint beta E p U x * E x.2)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) := by
  have step : ∀ x : M × B, finalJoint beta E p U x * Real.log (gibbs beta E x.2)
      = -beta * (finalJoint beta E p U x * E x.2)
        - Real.log (∑ b' : B, Real.exp (-beta * E b')) * finalJoint beta E p U x := by
    intro x
    rw [log_gibbs]
    ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, finalJoint_sum beta E p hp1 U, mul_one]

-- The core inequality: the drop in the memory's Shannon entropy is bounded by
-- `β` times the heat released into the bath.
include hp hp1 in
