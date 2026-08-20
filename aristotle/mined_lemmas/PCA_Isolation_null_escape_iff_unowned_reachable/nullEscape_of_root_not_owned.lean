/-
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

variable {α : Type*}

/-- An *isolate*: the abstract model used by the isolation engine.

* `edge a b` means the object `a` holds a reference to the object `b`;
* `owned` is the set of objects that belong to (are owned by) the isolate;
* `root` is the isolate's entry object.
-/
structure Isolate (α : Type*) where
  /-- `edge a b` holds when object `a` stores a reference to object `b`. -/
  edge : α → α → Prop
  /-- The set of objects owned by the isolate. -/
  owned : Set α
  /-- The entry object of the isolate. -/
  root : α

/-- `Reaches I a b` : `b` is reachable from `a` by following references. -/

theorem nullEscape_of_root_not_owned (I : Isolate α) (h : I.root ∉ I.owned) :
    NullEscape I :=
  nullEscape_of_unowned_reachable I Relation.ReflTransGen.refl h

end PCA.Isolation

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

