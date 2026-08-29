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

import Mathlib
import RequestProject.Savitch.Reach

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The deterministic simulator

This file defines the deterministic machine used in Savitch's theorem: an explicit
iterative (stack based) implementation of the recursive procedure

```
REACH d u v  =  if d = 0 then (u = v ∨ u → v)
                else ∃ m, REACH (d-1) u m ∧ REACH (d-1) m v
```

together with its encoding into bit strings and the space accounting: a well-formed
state occupies `O((f n)²)` bits, because the stack holds at most `f n + 2` frames of
`O(f n)` bits each.
-/

namespace CS
namespace Savitch

/-- Classical truth value of a proposition. -/

noncomputable def toDet (A : AbsMachine S) : DetMachine where
  head w := if A.enc (A.dec w) = w then A.head (A.dec w) else 0
  step w b := if A.enc (A.dec w) = w then A.enc (A.step (A.dec w) b) else w
  halt w := if A.enc (A.dec w) = w then A.halt (A.dec w) else true
  out w := if A.enc (A.dec w) = w then A.out (A.dec w) else false
  init := A.enc A.init
  halt_fix := by
    intro w b hw
    by_cases h : A.enc (A.dec w) = w
    · simp only [if_pos h] at hw ⊢
      rw [A.halt_fix _ _ hw, h]
    · simp only [if_neg h]

