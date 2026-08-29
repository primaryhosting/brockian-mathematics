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

lemma reach_iff_R (s : ℕ) (hsp : ∀ w, N.Reach x N.init w → w.length ≤ s) (v : Word) :
    N.Reach x N.init v ↔ R N x s (s + 1) N.init v := by
  constructor
  · intro h
    have h1 : ReachIn N x ((cands s).length) N.init v := reach_bounded N x s hsp h
    have h2 : ReachIn N x (2 ^ (s + 1)) N.init v :=
      ReachIn_mono N x (cands_length_le s) h1
    exact R_complete N x s hsp (s + 1) N.init v Relation.ReflTransGen.refl h2
  · intro h
    exact R_sound N x s (s + 1) N.init v h

end Savitch
end CS

