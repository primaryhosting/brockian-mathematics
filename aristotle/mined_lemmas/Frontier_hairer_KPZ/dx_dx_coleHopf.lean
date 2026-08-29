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

lemma dx_dx_coleHopf (H : Regular h) (t x : ℝ) :
    dx (dx (coleHopf h)) t x
      = Real.exp (h t x) * ((dx h t x) ^ 2 + dx (dx h) t x) := by
  have hfun : (fun y => dx (coleHopf h) t y)
      = fun y => Real.exp (h t y) * dx h t y := by
    funext y; exact dx_coleHopf H t y
  have hd : HasDerivAt (fun y => Real.exp (h t y) * dx h t y)
      (Real.exp (h t x) * dx h t x * dx h t x
        + Real.exp (h t x) * dx (dx h) t x) x :=
    ((hasDerivAt_space H t x).exp).mul (hasDerivAt_space2 H t x)
  have key : dx (dx (coleHopf h)) t x
      = deriv (fun y => Real.exp (h t y) * dx h t y) x :=
    congrArg (fun f => deriv f x) hfun
  rw [key, hd.deriv]; ring

/-- Time derivative of the Cole–Hopf transform. -/
