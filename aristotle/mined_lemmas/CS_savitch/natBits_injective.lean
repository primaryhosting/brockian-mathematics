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

lemma natBits_injective : Function.Injective natBits := by
  intro m n h
  have hl : Nat.size m = Nat.size n := by
    have := congrArg List.length h; simpa using this
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < Nat.size m
  · have := congrArg (fun l => l[i]?) h
    simp [natBits, hi, hl ▸ hi] at this
    simpa using this
  · have h1 : m < 2 ^ i :=
      lt_of_lt_of_le (Nat.lt_size_self m) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : n < 2 ^ i :=
      lt_of_lt_of_le (Nat.lt_size_self n) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

/-- Self-delimiting code of a single word: every bit is doubled and the code word
`[true, false]` is used as a terminator. -/
