/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The development below is therefore fully
self-contained in core Lean 4: it builds the small amount of graph theory it needs
(reflexive-transitive closure, and reference traces through the object graph) from scratch.
The two transfer lemmas `PCA.Isolation.reaches_of_chainFrom` and
`PCA.Isolation.exists_chainFrom_of_reaches` below play the role of Mathlib's
`List.relationReflTransGen_of_exists_isChain` and
`List.exists_isChain_ne_nil_of_relationReflTransGen`, which are the Mathlib lemmas that would
close these steps if Mathlib were available in this file.
-/

namespace PCA.Isolation

universe u

/-- An abstract model of an isolation engine's object graph.

* `root` marks the entry points (the capability roots the engine scans from);
* `edge a b` means object `a` holds a reference to object `b`;
* `owned v` means object `v` belongs to the isolation domain (it is *owned*).
-/
structure Model (V : Type u) where
  /-- The entry points of the object graph. -/
  root : V → Prop
  /-- `edge a b` holds when object `a` references object `b`. -/
  edge : V → V → Prop
  /-- `owned v` holds when `v` lies inside the isolation domain. -/
  owned : V → Prop

variable {V : Type u}

/-- Reflexive-transitive closure of a relation: `Reaches e a b` means `b` can be obtained
from `a` by following finitely many `e`-edges. -/
inductive Reaches (e : V → V → Prop) : V → V → Prop
  /-- Every object reaches itself. -/
  | refl (a : V) : Reaches e a a
  /-- Reachability extends along an edge. -/
  | tail {a b c : V} : Reaches e a b → e b c → Reaches e a c

/-- `v` is reachable in the model when some root reaches it along finitely many edges. -/
def Reachable (M : Model V) (v : V) : Prop :=
  ∃ r, M.root r ∧ Reaches M.edge r v

/-- The last object of the trace that starts at `a` and continues through `l`. -/
def lastOf (a : V) : List V → V
  | [] => a
  | b :: l => lastOf b l

/-- `chainFrom e a l` says that `a :: l` is a concrete `e`-path: consecutive objects are
linked by references. -/
def chainFrom (e : V → V → Prop) (a : V) : List V → Prop
  | [] => True
  | b :: l => e a b ∧ chainFrom e b l

/-- An *escape trace*: a concrete reference path `a :: l` that starts at a root and whose
final object is *not* owned by the isolation domain. This is the operational witness the
isolation engine's checker produces. -/
def EscapeTrace (M : Model V) (a : V) (l : List V) : Prop :=
  M.root a ∧ chainFrom M.edge a l ∧ ¬ M.owned (lastOf a l)

/-- The model exhibits a *null escape*: some concrete reference trace leaks out of the
isolation domain. -/
def NullEscape (M : Model V) : Prop :=
  ∃ a l, EscapeTrace M a l

/-- Reachability can also be extended at the head of a path. -/
theorem Reaches.head {e : V → V → Prop} {a b c : V} (hab : e a b) (h : Reaches e b c) :
    Reaches e a c := by
  induction h with
  | refl => exact Reaches.tail (Reaches.refl a) hab
  | tail _ hcd ih => exact Reaches.tail ih hcd

/-- Soundness of traces: following a concrete trace witnesses reachability of its last
object. (Mathlib analogue: `List.relationReflTransGen_of_exists_isChain`.) -/
theorem reaches_of_chainFrom {e : V → V → Prop} :
    ∀ (l : List V) (a : V), chainFrom e a l → Reaches e a (lastOf a l)
  | [], a, _ => Reaches.refl a
  | b :: l, _, h => Reaches.head h.1 (reaches_of_chainFrom l b h.2)

/-- Appending a further edge to a trace again gives a trace. -/
theorem chainFrom_append_edge {e : V → V → Prop} (l : List V) :
    ∀ (a c : V), chainFrom e a l → e (lastOf a l) c → chainFrom e a (l ++ [c]) := by
  induction l with
  | nil => intro _ _ _ hc; exact ⟨hc, trivial⟩
  | cons b l ih => intro _ c h hc; exact ⟨h.1, ih b c h.2 hc⟩

/-- The last object of an extended trace is the newly appended one. -/
theorem lastOf_append_singleton (l : List V) (a c : V) : lastOf a (l ++ [c]) = c := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih b

/-- Completeness of traces: a reachable object is the endpoint of a concrete trace.
(Mathlib analogue: `List.exists_isChain_ne_nil_of_relationReflTransGen`.) -/
theorem exists_chainFrom_of_reaches {e : V → V → Prop} {a v : V} (h : Reaches e a v) :
    ∃ l, chainFrom e a l ∧ lastOf a l = v := by
  induction h with
  | refl => exact ⟨[], trivial, rfl⟩
  | @tail b c _ hbc ih =>
      match ih with
      | ⟨l, hl, hlast⟩ =>
        exact ⟨l ++ [c], chainFrom_append_edge l a c hl (hlast ▸ hbc),
          lastOf_append_singleton l a c⟩

/-- **Soundness and completeness of the isolation model.** A null escape occurs exactly
when some reachable object is unowned. -/
theorem null_escape_iff_unowned_reachable (M : Model V) :
    NullEscape M ↔ ∃ v, Reachable M v ∧ ¬ M.owned v := by
  constructor
  · intro h
    match h with
    | ⟨a, l, hroot, hchain, hown⟩ =>
      exact ⟨lastOf a l, ⟨a, hroot, reaches_of_chainFrom l a hchain⟩, hown⟩
  · intro h
    match h with
    | ⟨v, ⟨r, hroot, hreach⟩, hown⟩ =>
      match exists_chainFrom_of_reaches hreach with
      | ⟨l, hl, hlast⟩ => exact ⟨r, l, hroot, hl, hlast ▸ hown⟩

/-- **Isolation soundness, contrapositive form.** The engine reports no escape exactly when
every reachable object is owned. -/
theorem no_null_escape_iff_forall_reachable_owned (M : Model V) :
    ¬ NullEscape M ↔ ∀ v, Reachable M v → M.owned v := by
  rw [null_escape_iff_unowned_reachable]
  constructor
  · intro h v hv
    by_cases ho : M.owned v
    · exact ho
    · exact absurd ⟨v, hv, ho⟩ h
  · intro h hex
    match hex with
    | ⟨v, hv, hown⟩ => exact hown (h v hv)

end PCA.Isolation

import Mathlib

/-!
# Null escape iff unowned reachable — Mathlib-flavoured companion

This file restates `PCA.Isolation.null_escape_iff_unowned_reachable` using Mathlib's own
`Relation.ReflTransGen` and `List.IsChain`, so that the two directions are closed by the
Mathlib transfer lemmas

* `List.relationReflTransGen_of_exists_isChain`
* `List.exists_isChain_ne_nil_of_relationReflTransGen`

The primary (import-free, self-contained) development lives in
`RequestProject/NullEscapeIffUnownedReachable.lean`; the required header comment there is a
module docstring, which Lean parses as a command, so that file cannot carry an `import` line.
-/

namespace PCA.Isolation.WithMathlib

/-- Object-graph model of the isolation engine: roots, reference edges, ownership. -/
structure Model (V : Type*) where
  /-- The entry points of the object graph. -/
  root : V → Prop
  /-- `edge a b` holds when object `a` references object `b`. -/
  edge : V → V → Prop
  /-- `owned v` holds when `v` lies inside the isolation domain. -/
  owned : V → Prop

variable {V : Type*} (M : Model V)

/-- `v` is reachable when some root reaches it along finitely many reference edges. -/
def Reachable (v : V) : Prop :=
  ∃ r, M.root r ∧ Relation.ReflTransGen M.edge r v

/-- A nonempty concrete reference path starting at a root and ending at an unowned object. -/
def EscapeTrace (p : List V) : Prop :=
  ∃ h : p ≠ [], List.IsChain M.edge p ∧ M.root (p.head h) ∧ ¬ M.owned (p.getLast h)

/-- Some reference trace leaks out of the isolation domain. -/
def NullEscape : Prop :=
  ∃ p : List V, EscapeTrace M p

/-- Soundness and completeness of the isolation model, phrased with Mathlib's
`Relation.ReflTransGen` and `List.IsChain`. -/
theorem null_escape_iff_unowned_reachable :
    NullEscape M ↔ ∃ v, Reachable M v ∧ ¬ M.owned v := by
  constructor
  · rintro ⟨p, hne, hchain, hroot, hown⟩
    exact ⟨p.getLast hne, ⟨p.head hne, hroot,
      List.relationReflTransGen_of_exists_isChain p hchain hne⟩, hown⟩
  · rintro ⟨v, ⟨r, hroot, hreach⟩, hown⟩
    obtain ⟨p, hne, hchain, hhead, hlast⟩ :=
      List.exists_isChain_ne_nil_of_relationReflTransGen hreach
    exact ⟨p, hne, hchain, hhead ▸ hroot, hlast ▸ hown⟩

end PCA.Isolation.WithMathlib

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

