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
def NullEscape (C : Config V) : Prop :=
  ∃ (v : V) (l : List V), Path C v l ∧ ¬ C.owned v

/-- The local check performed by the isolation engine: all roots are owned, and
ownership is preserved along every reference leaving a reachable owned object. -/
def Guarded (C : Config V) : Prop :=
  (∀ r : V, C.root r → C.owned r) ∧
    ∀ u v : V, Reaches C u → C.owned u → C.edge u v → C.owned v

/-- Every operational path witnesses declarative reachability. -/
theorem reaches_of_path {v : V} {l : List V} (h : Path C v l) : Reaches C v := by
  induction h with
  | start hr => exact Reaches.root hr
  | move _ he ih => exact Reaches.step ih he

/-- Conversely, every reachable object is reached by some concrete path. -/
theorem exists_path_of_reaches {v : V} (h : Reaches C v) : ∃ l : List V, Path C v l := by
  induction h with
  | root hr => exact ⟨[], Path.start hr⟩
  | @step u v _ he ih =>
      obtain ⟨l, hl⟩ := ih
      exact ⟨u :: l, Path.move hl he⟩

/-- **Main theorem.** The isolation engine reports a null escape exactly when the
abstract model has a reachable unowned object. This is simultaneously soundness
(no spurious reports) and completeness (no missed escapes) of the operational
escape check with respect to the declarative ownership model. -/
theorem null_escape_iff_unowned_reachable (C : Config V) :
    NullEscape C ↔ ∃ v : V, Reaches C v ∧ ¬ C.owned v := by
  constructor
  · rintro ⟨v, l, hp, hv⟩
    exact ⟨v, reaches_of_path hp, hv⟩
  · rintro ⟨v, hv, hnv⟩
    obtain ⟨l, hl⟩ := exists_path_of_reaches hv
    exact ⟨v, l, hl, hnv⟩

/-- Soundness of the engine's local check: if ownership is inductive along the
reachable part of the object graph, then no null escape is possible. -/
theorem not_nullEscape_of_guarded (hG : Guarded C) : ¬ NullEscape C := by
  obtain ⟨hroot, hstep⟩ := hG
  intro hE
  obtain ⟨v, hv, hnv⟩ := (null_escape_iff_unowned_reachable C).mp hE
  refine hnv ?_
  clear hnv hE
  induction hv with
  | root hr => exact hroot _ hr
  | @step u w hu he ih => exact hstep u w hu ih he

/-- Completeness of the engine's local check: if no null escape is possible,
then ownership is inductive along the reachable part of the object graph. -/
theorem guarded_of_not_nullEscape (h : ¬ NullEscape C) : Guarded C := by
  have key : ∀ v : V, Reaches C v → C.owned v := by
    intro v hv
    refine Classical.byContradiction fun hnv => ?_
    exact h ((null_escape_iff_unowned_reachable C).mpr ⟨v, hv, hnv⟩)
  exact ⟨fun r hr => key r (Reaches.root hr),
    fun u v hu _ he => key v (Reaches.step hu he)⟩

/-- The isolation engine is escape-free precisely when its local ownership check
succeeds. -/
theorem not_nullEscape_iff_guarded (C : Config V) : ¬ NullEscape C ↔ Guarded C :=
  ⟨guarded_of_not_nullEscape, not_nullEscape_of_guarded⟩

end PCA.Isolation

