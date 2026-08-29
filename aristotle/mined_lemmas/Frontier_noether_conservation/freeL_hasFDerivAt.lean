/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
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

/-- The partial derivative `∂L/∂q` of a one–dimensional Lagrangian
`L : ℝ × ℝ → ℝ` (first slot: position, second slot: velocity). -/

lemma freeL_hasFDerivAt (x v : ℝ) :
    HasFDerivAt freeL (v • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (x, v) := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) v v := by
    simpa using ((hasDerivAt_pow 2 v).div_const 2)
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (x, v) :=
    hasFDerivAt_snd
  have h := h1.comp_hasFDerivAt (x, v) hs
  simp only [Function.comp_def] at h
  exact h

