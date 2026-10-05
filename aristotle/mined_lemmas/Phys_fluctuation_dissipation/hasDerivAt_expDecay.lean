import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

/-- Derivative of an exponentially decaying observable `t ↦ c e^{-a t}`. -/

lemma hasDerivAt_expDecay (a c t : ℝ) :
    HasDerivAt (fun t : ℝ => c * Real.exp (-(a * t))) (-a * (c * Real.exp (-(a * t)))) t := by
  have h : HasDerivAt (fun t : ℝ => -(a * t)) (-a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).neg
  have h2 := (h.exp).const_mul c
  convert h2 using 1
  ring

/-- Uniqueness for the linear relaxation equation `f' = -a f`: a solution is determined
by its value at time `0`, and is the exponential decay `t ↦ f 0 * e^{-a t}`. -/
