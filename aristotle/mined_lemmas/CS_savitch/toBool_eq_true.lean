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

@[simp] lemma toBool_eq_true {P : Prop} : toBool P = true ↔ P := by
  simp [toBool, @decide_eq_true_iff P (Classical.propDecidable P)]

/-- A frame of the recursion stack: the recursion depth `level`, the endpoints `u`, `v`
of the subproblem, the `phase` of the frame (0: freshly entered, 1: waiting for the
first recursive call, 2: waiting for the second one) and the index `idx` of the
midpoint candidate currently being tried. -/
structure Frame where
  /-- Recursion depth of this subproblem. -/
  level : ℕ
  /-- Source configuration. -/
  u : Word
  /-- Target configuration. -/
  v : Word
  /-- Phase of the frame. -/
  phase : ℕ
  /-- Index of the midpoint candidate currently tried. -/
  idx : ℕ

/-- States of the deterministic simulator. -/
inductive SavState where
  /-- Measuring the length of the input; the head is at position `k`. -/
  | count (k : ℕ)
  /-- Looking for an accepting configuration; `j` is the index of the candidate. -/
  | scan (n j : ℕ)
  /-- Running the recursion for the target candidate `j` with the given stack and the
  boolean returned by the last completed call. -/
  | main (n j : ℕ) (st : List Frame) (ret : Bool)
  /-- Halted with output `b`. -/
  | done (b : Bool)

/-- Position of the input head in a given state. -/
