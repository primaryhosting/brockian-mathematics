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

lemma stateRegs_inj : Function.Injective stateRegs := by
  intro a b h
  cases a with
  | count k =>
    cases b with
    | count k' =>
      simp only [stateRegs, List.cons.injEq, and_true, true_and] at h
      rw [natBits_injective h]
    | scan n j => exfalso; simp [stateRegs] at h
    | main n j st r => exfalso; simp [stateRegs] at h
    | done c => exfalso; simp [stateRegs] at h
  | scan n j =>
    cases b with
    | count k' => exfalso; simp [stateRegs] at h
    | scan n' j' =>
      simp only [stateRegs, List.cons.injEq, and_true, true_and] at h
      rw [natBits_injective h.1, natBits_injective h.2]
    | main n' j' st r => exfalso; simp [stateRegs] at h
    | done c => exfalso; simp [stateRegs] at h
  | main n j st r =>
    cases b with
    | count k' => exfalso; simp [stateRegs] at h
    | scan n' j' => exfalso; simp [stateRegs] at h
    | main n' j' st' r' =>
      simp only [stateRegs, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rw [natBits_injective h1, natBits_injective h2,
        show r = r' from by simpa using h3, flatMap_frameRegs_inj st st' h4]
    | done c => exfalso; simp [stateRegs] at h
  | done c =>
    cases b with
    | count k' => exfalso; simp [stateRegs] at h
    | scan n' j' => exfalso; simp [stateRegs] at h
    | main n' j' st' r' => exfalso; simp [stateRegs] at h
    | done c' =>
      simp only [stateRegs, List.cons.injEq, and_true, true_and] at h
      rw [show c = c' from by simpa using h]

