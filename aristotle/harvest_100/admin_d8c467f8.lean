/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u

/-- Abstract model of the isolation engine's heap-with-ownership view.

* `edge a b` means the object `a` holds a reference to the object `b`;
* `owned v` means the isolation engine holds an ownership capability for `v`
  (an *unowned* object models a null / foreign / escaped capability);
* `root r` marks the entry points visible to the component under analysis. -/
structure Heap (V : Type u) where
  /-- Reference edges of the heap graph. -/
  edge : V → V → Prop
  /-- Ownership capability predicate. -/
  owned : V → Prop
  /-- Entry points of the component. -/
  root : V → Prop

variable {V : Type u}

/-- Reachability along reference edges (reflexive–transitive closure of `e`). -/
inductive Reach (e : V → V → Prop) : V → V → Prop
  /-- Every object reaches itself. -/
  | refl (a : V) : Reach e a a
  /-- Prefixing a reference edge to a reachability witness. -/
  | head {a b c : V} : e a b → Reach e b c → Reach e a c

/-- Appending a reference edge at the end of a reachability witness. -/
theorem Reach.tail {e : V → V → Prop} {a b c : V} (hab : Reach e a b) (hbc : e b c) :
    Reach e a c := by
  induction hab with
  | refl a => exact Reach.head hbc (Reach.refl c)
  | head h _ ih => exact Reach.head h (ih hbc)

/-- `IsPath e a l` says that `a :: l` is a concrete finite access trace: every
consecutive pair of objects in it is linked by a reference edge. -/
def IsPath (e : V → V → Prop) : V → List V → Prop
  | _, [] => True
  | a, b :: l => e a b ∧ IsPath e b l

/-- The object an access trace `a :: l` ends at. -/
def traceTarget : V → List V → V
  | a, [] => a
  | _, b :: l => traceTarget b l

/-- Operational statement of a null escape: some finite access trace starting at
a root ends at an object for which no ownership capability is held. -/
def NullEscapes (H : Heap V) : Prop :=
  ∃ (r : V) (l : List V), H.root r ∧ IsPath H.edge r l ∧ ¬ H.owned (traceTarget r l)

/-- Declarative statement: some unowned object is reachable from a root. -/
def UnownedReachable (H : Heap V) : Prop :=
  ∃ r v : V, H.root r ∧ Reach H.edge r v ∧ ¬ H.owned v

/-- Every access trace witnesses reachability of its target. -/
theorem reach_traceTarget (e : V → V → Prop) :
    ∀ (a : V) (l : List V), IsPath e a l → Reach e a (traceTarget a l)
  | a, [], _ => Reach.refl a
  | _, b :: l, h => Reach.head h.1 (reach_traceTarget e b l h.2)

/-- Every reachability witness is realized by a concrete access trace. -/
theorem exists_path_of_reach {e : V → V → Prop} {a v : V} (h : Reach e a v) :
    ∃ l : List V, IsPath e a l ∧ traceTarget a l = v := by
  induction h with
  | refl _ => exact ⟨[], trivial, rfl⟩
  | head hab _ ih =>
      obtain ⟨l, hl, hlast⟩ := ih
      exact ⟨_ :: l, ⟨hab, hl⟩, hlast⟩

/-- **Soundness and completeness of the isolation engine's model**: the
trace-based (operational) notion of a null escape coincides exactly with the
reachability-based (declarative) notion of an unowned object being reachable
from a root. -/
theorem null_escape_iff_unowned_reachable (H : Heap V) :
    NullEscapes H ↔ UnownedReachable H := by
  constructor
  · rintro ⟨r, l, hr, hpath, hun⟩
    exact ⟨r, traceTarget r l, hr, reach_traceTarget H.edge r l hpath, hun⟩
  · rintro ⟨r, v, hr, hreach, hun⟩
    obtain ⟨l, hl, hlast⟩ := exists_path_of_reach hreach
    exact ⟨r, l, hr, hl, hlast ▸ hun⟩

/-- An edge-closed predicate is preserved along reachability. -/
theorem Reach.closed {e : V → V → Prop} {I : V → Prop}
    (hclosed : ∀ a, I a → ∀ b, e a b → I b) {a b : V} (hab : Reach e a b) (ha : I a) : I b := by
  induction hab with
  | refl _ => exact ha
  | head hxy _ ih => exact ih (hclosed _ ha _ hxy)

/-- Certificate form (soundness of an ownership invariant): if an invariant `I`
covers the roots, is closed under reference edges, and contains only owned
objects, then no null escape is possible. -/
theorem no_null_escape_of_owned_invariant (H : Heap V) (I : V → Prop)
    (hroots : ∀ r, H.root r → I r)
    (hclosed : ∀ a, I a → ∀ b, H.edge a b → I b)
    (howned : ∀ a, I a → H.owned a) :
    ¬ NullEscapes H := by
  rw [null_escape_iff_unowned_reachable]
  rintro ⟨r, v, hr, hreach, hun⟩
  exact hun (howned v (Reach.closed hclosed hreach (hroots r hr)))

/-- Conversely, the absence of null escapes is always witnessed by such an
invariant, namely the set of objects reachable from the roots; so the
certificate rule above is complete as well. -/
theorem exists_owned_invariant_of_no_null_escape (H : Heap V) (h : ¬ NullEscapes H) :
    ∃ I : V → Prop, (∀ r, H.root r → I r) ∧ (∀ a, I a → ∀ b, H.edge a b → I b) ∧
      (∀ a, I a → H.owned a) := by
  refine ⟨fun v => ∃ r, H.root r ∧ Reach H.edge r v, fun r hr => ⟨r, hr, Reach.refl r⟩, ?_, ?_⟩
  · rintro a ⟨r, hr, hra⟩ b hab
    exact ⟨r, hr, hra.tail hab⟩
  · rintro a ⟨r, hr, hra⟩
    exact Classical.byContradiction fun hun =>
      h ((null_escape_iff_unowned_reachable H).2 ⟨r, a, hr, hra, hun⟩)

/-! ### Nontriviality checks -/

/-- A two-object heap whose root points at an unowned object really does escape. -/
example : NullEscapes (V := Bool)
    ⟨fun a b => a = true ∧ b = false, fun v => v = true, fun r => r = true⟩ :=
  ⟨true, [false], rfl, ⟨⟨rfl, rfl⟩, trivial⟩, by simp [traceTarget]⟩

/-- A heap all of whose objects are owned has no null escape. -/
example (H : Heap V) (h : ∀ v, H.owned v) : ¬ NullEscapes H :=
  no_null_escape_of_owned_invariant H (fun _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun a _ => h a)

end PCA.Isolation

import Mathlib
import RequestProject.NullEscape


/-!
# Null Escape Iff Unowned Reachable — Mathlib bridge

Category: Proof-Carrying Apps
Target: `PCA.Isolation.null_escape_iff_unowned_reachable` (see `RequestProject/NullEscape.lean`)
Provenance: Aristotle theorem prover (Harmonic)

The target theorem is stated and proved dependency-free in `RequestProject/NullEscape.lean`
(its required header comment must be the very first thing in that file, and Lean forbids
`import` commands after a comment-level command, so that file carries no imports).

This file connects that development to Mathlib's own vocabulary: the model's reachability
relation is Mathlib's `Relation.ReflTransGen`, its access traces are Mathlib's `List.IsChain`,
and the target equivalence is restated with `Set`-valued roots.
-/


set_option autoImplicit false

namespace PCA.Isolation

universe u

variable {V : Type u}

/-- The model's reachability relation is exactly Mathlib's reflexive–transitive closure. -/
theorem reach_iff_reflTransGen (e : V → V → Prop) (a b : V) :
    Reach e a b ↔ Relation.ReflTransGen e a b := by
  constructor
  · intro h
    induction h with
    | refl _ => exact .refl
    | head hxy _ ih => exact Relation.ReflTransGen.head hxy ih
  · intro h
    induction h with
    | refl => exact Reach.refl a
    | tail _ hbc ih => exact ih.tail hbc

/-- The model's access traces are exactly Mathlib's `List.IsChain`s. -/
theorem isPath_iff_isChain (e : V → V → Prop) :
    ∀ (a : V) (l : List V), IsPath e a l ↔ List.IsChain e (a :: l)
  | _, [] => by simp [IsPath]
  | a, b :: l => by
      rw [IsPath, List.isChain_cons_cons, isPath_iff_isChain e b l]

/-- The model's trace endpoint is the last element of the trace. -/
theorem traceTarget_eq_getLast :
    ∀ (a : V) (l : List V), traceTarget a l = (a :: l).getLast (List.cons_ne_nil _ _)
  | _, [] => rfl
  | a, b :: l => by
      rw [traceTarget, traceTarget_eq_getLast b l]
      simp

/-- Mathlib-phrased restatement of the target theorem, with `Set`-valued roots, `List.IsChain`
access traces and `Relation.ReflTransGen` reachability:

an access trace from a root ends at an object with no ownership capability **iff** some
object with no ownership capability is reachable from a root. -/
theorem null_escape_iff_unowned_reachable_mathlib
    (edge : V → V → Prop) (owned : V → Prop) (roots : Set V) :
    (∃ (r : V) (l : List V), r ∈ roots ∧ List.IsChain edge (r :: l) ∧
        ¬ owned ((r :: l).getLast (List.cons_ne_nil _ _)))
      ↔ ∃ r ∈ roots, ∃ v, Relation.ReflTransGen edge r v ∧ ¬ owned v := by
  have key := null_escape_iff_unowned_reachable
    (⟨edge, owned, fun r => r ∈ roots⟩ : Heap V)
  simp only [NullEscapes, UnownedReachable] at key
  constructor
  · rintro ⟨r, l, hr, hchain, hun⟩
    obtain ⟨r', v, hr', hreach, hun'⟩ :=
      key.1 ⟨r, l, hr, (isPath_iff_isChain edge r l).2 hchain, by
        rwa [traceTarget_eq_getLast]⟩
    exact ⟨r', hr', v, (reach_iff_reflTransGen edge r' v).1 hreach, hun'⟩
  · rintro ⟨r, hr, v, hreach, hun⟩
    obtain ⟨r', l, hr', hpath, hun'⟩ :=
      key.2 ⟨r, v, hr, (reach_iff_reflTransGen edge r v).2 hreach, hun⟩
    exact ⟨r', l, hr', (isPath_iff_isChain edge r' l).1 hpath, by
      rwa [traceTarget_eq_getLast] at hun'⟩

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

