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

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

universe u

variable {Node : Type u}

/-- An abstract model of the object graph maintained by the isolation engine.

* `edge u v` : object `u` holds a reference to object `v`;
* `sealed u` : the isolation engine forbids dereferencing out of `u`
  (an opaque, capability-protected object);
* `owned u`  : object `u` belongs to some realm (it is *not* a null-owner object);
* `roots u`  : `u` is one of the objects initially handed to the untrusted component. -/
structure Heap (Node : Type u) where
  /-- `edge u v` means object `u` holds a reference to object `v`. -/
  edge : Node → Node → Prop
  /-- `sealed u` means the engine forbids dereferencing out of `u`. -/
  sealed : Node → Prop
  /-- `owned u` means object `u` belongs to some realm. -/
  owned : Node → Prop
  /-- `roots u` means `u` is handed to the untrusted component at start-up. -/
  roots : Node → Prop

/-- The dereference step actually permitted by the isolation engine: one may follow an
edge out of `u` only when `u` is not sealed. -/

theorem reachable_of_trace (H : Heap Node) {n : Node} {l : List Node}
    (h : Trace H (n :: l)) :
    ∃ r : Node, H.roots r ∧ H.Reach r n := by
  generalize hl : n :: l = L at h
  induction h generalizing n l with
  | @root r hr =>
      cases hl
      exact ⟨r, hr, Heap.Reach.refl r⟩
  | @step u v l' _ hstep ih =>
      cases hl
      obtain ⟨r, hr, hpath⟩ := ih rfl
      exact ⟨r, hr, hpath.tail hstep⟩

/-- Conversely, any object reachable from a root is the current object of some trace. -/
