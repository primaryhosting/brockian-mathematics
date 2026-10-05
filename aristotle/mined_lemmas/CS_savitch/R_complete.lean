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

lemma R_complete (s : ℕ) (hsp : ∀ w, N.Reach x N.init w → w.length ≤ s) :
    ∀ (d : ℕ) (u v : Word), N.Reach x N.init u → ReachIn N x (2 ^ d) u v → R N x s d u v := by
  intro d
  induction d with
  | zero =>
    intro u v _ h
    obtain ⟨j, hj, hs⟩ := h
    interval_cases j
    · exact Or.inl hs
    · obtain ⟨m, hm, hmv⟩ := hs
      rw [show u = m from hm]
      exact Or.inr hmv
  | succ d ih =>
    intro u v hu h
    have hsplit : (2 : ℕ) ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    rw [hsplit] at h
    obtain ⟨m, h1, h2⟩ := ReachIn_split N x _ _ u v h
    have hm : N.Reach x N.init m := hu.trans (ReachIn_reach N x h1)
    exact ⟨m, mem_cands.2 (hsp m hm), ih u m hu h1, ih m v hm h2⟩

/-- Reachability from the initial configuration is exactly the Savitch predicate at
depth `s + 1`, for machines all of whose reachable configurations have length ≤ `s`. -/
