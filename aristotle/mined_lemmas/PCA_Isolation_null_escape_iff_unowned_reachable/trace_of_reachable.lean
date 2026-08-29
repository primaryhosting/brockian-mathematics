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

theorem trace_of_reachable (H : Heap Node) {r n : Node} (hr : H.roots r)
    (h : H.Reach r n) :
    ∃ l : List Node, Trace H (n :: l) := by
  induction h with
  | refl => exact ⟨[], Trace.root hr⟩
  | tail _ hstep ih =>
      obtain ⟨l, hl⟩ := ih
      exact ⟨_, hl.step hstep⟩

/-- **Soundness and completeness of the isolation engine's static check.**
The untrusted component can get hold of an unowned ("null-owner") object during some
execution if and only if an unowned object is reachable from a root along permitted
dereference steps. -/
