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

/-- The spatial partial derivative of a space-time function `h : ℝ → ℝ → ℝ`
(first argument = time, second argument = space). -/

lemma regular_log (HZ : Regular Z) (hpos : ∀ t x, 0 < Z t x) :
    Regular (fun t x => Real.log (Z t x)) where
  time := fun x => (HZ.time x).log (fun t => (hpos t x).ne')
  space := fun t => (HZ.space t).log (fun x => (hpos t x).ne')
  space2 := fun t => by
    have hfun : (fun y => dx (fun t x => Real.log (Z t x)) t y)
        = fun y => dx Z t y / Z t y := by
      funext y; exact dx_log HZ hpos t y
    rw [hfun]
    exact (HZ.space2 t).div (HZ.space t) (fun y => (hpos t y).ne')

/-- The Cole–Hopf transform inverts the logarithm on positive functions. -/
