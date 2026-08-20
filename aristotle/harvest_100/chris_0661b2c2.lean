/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u v

/-- An abstract model of the object graph tracked by an isolation engine.

* `Node` is the type of heap locations (objects / capabilities).
* `Region` is the type of ownership regions (isolates, arenas, owners, ...).
* `edge a b` holds when object `a` holds a reference to object `b`.
* `owner v` is the owning region of `v`, with `none` meaning *unowned*
  (a "null owner": the object belongs to no region).
* `root` is the entry capability from which the engine explores the graph.
-/
structure Heap (Node : Type u) (Region : Type v) where
  /-- `edge a b` means `a` holds a reference to `b`. -/
  edge : Node → Node → Prop
  /-- The owning region of a node, `none` for an unowned node. -/
  owner : Node → Option Region
  /-- The root capability of the isolate. -/
  root : Node

/-- Reflexive-transitive closure of a relation: `Reaches r a b` holds when `b` can be
obtained from `a` by following finitely many `r`-steps. -/
inductive Reaches {Node : Type u} (r : Node → Node → Prop) : Node → Node → Prop
  /-- Zero steps. -/
  | refl (a : Node) : Reaches r a a
  /-- One step followed by a further walk. -/
  | head {a b c : Node} : r a b → Reaches r b c → Reaches r a c

/-- `IsChain r l` says that consecutive entries of `l` are related by `r`. -/
def IsChain {Node : Type u} (r : Node → Node → Prop) : List Node → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => r a b ∧ IsChain r (b :: t)

variable {Node : Type u} {Region : Type v} (H : Heap Node Region)

/-- A node is *unowned* when its owner field is null. -/
def Unowned (v : Node) : Prop := H.owner v = none

/-- A node is *reachable* when the engine can walk to it from the root by dereferencing
references. -/
def Reachable (v : Node) : Prop := Reaches H.edge H.root v

/-- An *access trace* of the isolation engine: a list of nodes starting at the root, where
each successive node is obtained by dereferencing the previous one. -/
def IsTrace (l : List Node) : Prop :=
  IsChain H.edge l ∧ l.head? = some H.root

/-- A *null escape*: some access trace of the engine ends at an unowned node, i.e. an
object with a null owner is exposed at the isolate boundary. -/
def NullEscape : Prop :=
  ∃ (l : List Node) (v : Node), IsTrace H l ∧ l.getLast? = some v ∧ Unowned H v

/-- Some unowned node is reachable from the root. -/
def UnownedReachable : Prop :=
  ∃ v : Node, Reachable H v ∧ Unowned H v

variable {H}

/-- A chain starting at `a` and ending at `v` witnesses that `v` is reached from `a`. -/
theorem reaches_of_isChain_cons {a v : Node} :
    ∀ (t : List Node), IsChain H.edge (a :: t) → (a :: t).getLast? = some v →
      Reaches H.edge a v := by
  intro t
  induction t generalizing a with
  | nil =>
    intro _ hlast
    have : a = v := by simpa using hlast
    exact this ▸ Reaches.refl a
  | cons b t ih =>
    intro hchain hlast
    obtain ⟨hab, hrest⟩ := hchain
    exact Reaches.head hab (ih hrest (by simpa using hlast))

/-- Conversely, whenever `v` is reached from `a` there is an explicit chain from `a`
to `v`. -/
theorem exists_isChain_cons_of_reaches {a v : Node} (h : Reaches H.edge a v) :
    ∃ t : List Node, IsChain H.edge (a :: t) ∧ (a :: t).getLast? = some v := by
  induction h with
  | refl a => exact ⟨[], trivial, rfl⟩
  | head hab _ ih =>
    obtain ⟨t, hchain, hlast⟩ := ih
    exact ⟨_ :: t, ⟨hab, hchain⟩, by simpa using hlast⟩

/-- Every trace ending at `v` witnesses reachability of `v`. -/
theorem reachable_of_isTrace {l : List Node} {v : Node}
    (hl : IsTrace H l) (hv : l.getLast? = some v) : Reachable H v := by
  obtain ⟨hchain, hhead⟩ := hl
  match l with
  | [] => simp at hhead
  | a :: t =>
    have ha : a = H.root := by simpa using hhead
    subst ha
    exact reaches_of_isChain_cons t hchain hv

/-- Every reachable node is the endpoint of some access trace. -/
theorem exists_trace_of_reachable {v : Node} (hv : Reachable H v) :
    ∃ l : List Node, IsTrace H l ∧ l.getLast? = some v := by
  obtain ⟨t, hchain, hlast⟩ := exists_isChain_cons_of_reaches hv
  exact ⟨H.root :: t, ⟨hchain, rfl⟩, hlast⟩

/-- **Soundness and completeness of the isolation engine's escape model.**

A null escape occurs exactly when some unowned node is reachable from the root. -/
theorem null_escape_iff_unowned_reachable :
    NullEscape H ↔ UnownedReachable H := by
  constructor
  · rintro ⟨l, v, hl, hv, hun⟩
    exact ⟨v, reachable_of_isTrace hl hv, hun⟩
  · rintro ⟨v, hreach, hun⟩
    obtain ⟨l, hl, hv⟩ := exists_trace_of_reachable hreach
    exact ⟨l, v, hl, hv, hun⟩

/-- Soundness: a null escape exhibited by a trace really does reach an unowned node. -/
theorem unowned_reachable_of_null_escape (h : NullEscape H) : UnownedReachable H :=
  null_escape_iff_unowned_reachable.mp h

/-- Completeness: any reachable unowned node yields a concrete escaping trace. -/
theorem null_escape_of_unowned_reachable (h : UnownedReachable H) : NullEscape H :=
  null_escape_iff_unowned_reachable.mpr h

/-- Isolation holds (no null escape) exactly when every reachable node is owned. -/
theorem not_null_escape_iff_forall_reachable_owned :
    ¬ NullEscape H ↔ ∀ v : Node, Reachable H v → ∃ r : Region, H.owner v = some r := by
  rw [null_escape_iff_unowned_reachable]
  constructor
  · intro h v hv
    cases hov : H.owner v with
    | none => exact absurd ⟨v, hv, hov⟩ h
    | some r => exact ⟨r, rfl⟩
  · rintro h ⟨v, hv, hun⟩
    obtain ⟨r, hr⟩ := h v hv
    rw [Unowned, hr] at hun
    simp at hun

/-! ### Non-vacuity: both sides of the equivalence are realizable -/

/-- A three-object heap: the root references `child`, which references `orphan`. -/
inductive Obj where
  /-- The isolate's root capability. -/
  | root : Obj
  /-- An object owned by the isolate. -/
  | child : Obj
  /-- An object with a null owner. -/
  | orphan : Obj
  deriving DecidableEq

/-- The single ownership region of the examples. -/
inductive Reg where
  /-- The isolate itself. -/
  | iso : Reg

/-- References of the example heap: `root → child → orphan`. -/
def exEdge : Obj → Obj → Prop
  | .root, .child => True
  | .child, .orphan => True
  | _, _ => False

/-- A heap in which the unowned object `orphan` is reachable. -/
def leakyHeap : Heap Obj Reg where
  edge := exEdge
  owner := fun o => match o with
    | .orphan => none
    | _ => some .iso
  root := .root

/-- A heap with the same shape in which every object is owned. -/
def safeHeap : Heap Obj Reg where
  edge := exEdge
  owner := fun _ => some .iso
  root := .root

example : NullEscape leakyHeap := by
  refine null_escape_of_unowned_reachable ⟨Obj.orphan, ?_, rfl⟩
  exact Reaches.head (b := Obj.child) trivial
    (Reaches.head (b := Obj.orphan) trivial (Reaches.refl _))

example : ¬ NullEscape safeHeap :=
  not_null_escape_iff_forall_reachable_owned.mpr fun _ _ => ⟨Reg.iso, rfl⟩

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

