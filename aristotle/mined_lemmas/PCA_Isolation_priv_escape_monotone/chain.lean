import Mathlib

/-!
# A formal model of a privilege-isolation engine

We model an *isolation policy* on a finite set of compartments `C` as a boolean
edge relation `edge : C → C → Bool`, where `edge a b = true` means that a
principal running in compartment `a` is permitted to influence / reach
compartment `b` (a channel that is *not* isolated).

The *ground truth* semantics of privilege escape is reachability
(`PCA.Isolation.Policy.Reach`, the reflexive transitive closure of `edge`).

The *engine* is a concrete computation: iterate a one-step expansion
`Policy.step` starting from `{s}`, `Fintype.card C` times
(`Policy.escape`).  We prove:

* `Policy.escape_sound`    – the engine never over-approximates,
* `Policy.escape_complete` – the engine never under-approximates,
* `Policy.mem_escape_iff`  – hence the engine decides reachability exactly,
* `PCA.Isolation.priv_escape_monotone` – weakening the isolation (adding
  permitted edges) can only increase the set of privileges reachable from a
  compartment.
-/

namespace PCA.Isolation

open Finset

/-- An isolation policy on a set of compartments `C`: `edge a b` says that
compartment `a` may influence compartment `b`. -/
structure Policy (C : Type*) where
  /-- `edge a b = true` means the channel from `a` to `b` is *not* isolated. -/
  edge : C → C → Bool

variable {C A : Type*} [Fintype C] [DecidableEq C]

/-- Privilege escape, semantically: `Reach P s d` iff `d` is reachable from `s`
along permitted channels. -/

def chain : PCA.Isolation.Policy (Fin 3) where
  edge a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

example : chain.escape 0 = {0, 1, 2} := by decide

example : chain.escape 2 = {2} := by decide

end Example

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

