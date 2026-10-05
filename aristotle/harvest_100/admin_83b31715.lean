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
def Heap.step (H : Heap Node) (u v : Node) : Prop := H.edge u v ∧ ¬ H.sealed u

/-- Reflexive-transitive closure of the permitted dereference step: `H.Reach r n` says
that `n` can be reached from `r` by finitely many permitted dereferences. -/
inductive Heap.Reach (H : Heap Node) : Node → Node → Prop
  | refl (r : Node) : H.Reach r r
  | tail {r u v : Node} : H.Reach r u → H.step u v → H.Reach r v

/-- Operational semantics of the untrusted component: `Trace H l` says that `l` is a
nonempty execution history, recorded most-recent-first, that starts at a root and
proceeds by permitted dereference steps. The head of `l` is the object the component
currently holds. -/
inductive Trace (H : Heap Node) : List Node → Prop
  | root {r : Node} : H.roots r → Trace H [r]
  | step {u v : Node} {l : List Node} :
      Trace H (u :: l) → H.step u v → Trace H (v :: u :: l)

/-- A *null escape*: some execution of the untrusted component ends up holding an
object that has no owning realm. -/
def Heap.NullEscape (H : Heap Node) : Prop :=
  ∃ (n : Node) (l : List Node), Trace H (n :: l) ∧ ¬ H.owned n

/-- The static (graph-theoretic) side condition checked by the isolation engine:
some unowned object is reachable from a root through permitted dereference steps. -/
def Heap.UnownedReachable (H : Heap Node) : Prop :=
  ∃ r n : Node, H.roots r ∧ H.Reach r n ∧ ¬ H.owned n

/-- Every trace starts at a root, and its current object is reachable from that root. -/
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
theorem null_escape_iff_unowned_reachable (H : Heap Node) :
    H.NullEscape ↔ H.UnownedReachable := by
  constructor
  · rintro ⟨n, l, htr, hn⟩
    obtain ⟨r, hr, hpath⟩ := reachable_of_trace H htr
    exact ⟨r, n, hr, hpath, hn⟩
  · rintro ⟨r, n, hr, hpath, hn⟩
    obtain ⟨l, hl⟩ := trace_of_reachable H hr hpath
    exact ⟨n, l, hl, hn⟩

/-! ### Sanity checks: both sides of the equivalence are satisfiable and refutable. -/

/-- A two-object heap `0 → 1` where `1` is unowned and `0` is not sealed: the untrusted
component really can escape. -/
def leakyHeap : Heap Bool where
  edge u v := u = false ∧ v = true
  sealed _ := False
  owned u := u = false
  roots u := u = false

example : leakyHeap.NullEscape := by
  refine ⟨true, [false], Trace.step (Trace.root rfl) ⟨⟨rfl, rfl⟩, id⟩, ?_⟩
  simp [leakyHeap]

/-- Sealing the root closes the leak. -/
def sealedHeap : Heap Bool where
  edge u v := u = false ∧ v = true
  sealed _ := True
  owned u := u = false
  roots u := u = false

example : ¬ sealedHeap.NullEscape := by
  rw [null_escape_iff_unowned_reachable]
  rintro ⟨r, n, hr, hpath, hn⟩
  induction hpath with
  | refl => exact hn (by simpa [sealedHeap] using hr)
  | tail _ hstep _ => exact hstep.2 trivial

end PCA.Isolation

