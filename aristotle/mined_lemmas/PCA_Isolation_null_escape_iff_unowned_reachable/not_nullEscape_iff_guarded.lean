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

universe u

namespace PCA.Isolation

/-- A configuration of the isolation engine's abstract model of a program state.

* `root` marks the entry points of the object graph (globals, stack roots, ...);
* `edge u v` means that object `u` holds a reference to object `v`;
* `owned v` means that `v` carries an ownership capability, i.e. it is confined
  inside the isolation domain. An object that is *not* owned is called *unowned*
  (a "null" reference from the point of view of the ownership discipline). -/
structure Config (V : Type u) where
  /-- Entry points of the object graph. -/
  root : V → Prop
  /-- `edge u v`: object `u` holds a reference to object `v`. -/
  edge : V → V → Prop
  /-- `owned v`: object `v` carries an ownership capability. -/
  owned : V → Prop

variable {V : Type u} {C : Config V}

/-- Declarative reachability: the least predicate containing the roots and
closed under following references. -/
inductive Reaches (C : Config V) : V → Prop
  | root {r : V} : C.root r → Reaches C r
  | step {u v : V} : Reaches C u → C.edge u v → Reaches C v

/-- Operational semantics of the isolation engine: `Path C v l` says that the
engine can walk from a root to `v`, having already visited exactly the objects
in `l` (most recent first). -/
inductive Path (C : Config V) : V → List V → Prop
  | start {r : V} : C.root r → Path C r []
  | move {u v : V} {l : List V} : Path C u l → C.edge u v → Path C v (u :: l)

/-- A **null escape** occurs when some concrete execution path of the engine
exposes an unowned ("null") object. -/

theorem not_nullEscape_iff_guarded (C : Config V) : ¬ NullEscape C ↔ Guarded C :=
  ⟨guarded_of_not_nullEscape, not_nullEscape_of_guarded⟩

end PCA.Isolation

