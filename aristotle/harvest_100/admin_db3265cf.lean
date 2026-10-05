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

/-!
## The isolation model

The state of a proof-carrying app's isolation engine is modelled as an
*ownership graph*:

* `Node` — the abstract locations (objects, cells, capabilities) of the heap;
* `edge` — the may-point-to relation computed by the engine;
* `roots` — the locations directly exposed to the (untrusted) outside world;
* `owner` — the ownership labelling; `owner n = none` means the location is
  *unowned* (a "null" owner), i.e. it belongs to no isolation domain.

The engine's operational notion of failure is a **null escape**: the forward
taint analysis `Flows`, propagated from the roots along `edge`, marks a location
whose owner is null.  The model-level notion of failure is `UnownedReachable`:
some unowned location is reachable from a root.

The main theorem `null_escape_iff_unowned_reachable` states that the two
coincide; its two directions are exactly completeness
(`unownedReachable_of_nullEscape`) and soundness
(`not_unownedReachable_of_not_nullEscape`) of the engine's model.  A third,
witness-based characterisation via explicit escape traces
(`null_escape_iff_hasEscapeTrace`) is also proved equivalent, so that a failing
analysis always yields a concrete counterexample trace, and conversely any such
trace is a real escape.

The development is deliberately self-contained (no imports), so that the header
comment above is literally the first thing in the file.
-/

namespace PCA
namespace Isolation

universe u v

variable {Node : Type u} {Owner : Type v}

/-- Reachability along `edge`: the reflexive–transitive closure. -/
inductive Reach (edge : Node → Node → Prop) (a : Node) : Node → Prop
  | refl : Reach edge a a
  | tail {b c : Node} (hb : Reach edge a b) (h : edge b c) : Reach edge a c

/-- Forward taint propagation performed by the isolation engine: the locations
the engine considers exposed to the outside world. -/
inductive Flows (roots : Node → Prop) (edge : Node → Node → Prop) : Node → Prop
  | root {n : Node} (hn : roots n) : Flows roots edge n
  | step {n m : Node} (hn : Flows roots edge n) (h : edge n m) : Flows roots edge m

/-- The engine reports a **null escape**: some exposed location is unowned. -/
def NullEscape (roots : Node → Prop) (edge : Node → Node → Prop)
    (owner : Node → Option Owner) : Prop :=
  ∃ n, Flows roots edge n ∧ owner n = none

/-- Model-level failure: some unowned location is reachable from a root. -/
def UnownedReachable (roots : Node → Prop) (edge : Node → Node → Prop)
    (owner : Node → Option Owner) : Prop :=
  ∃ r n, roots r ∧ Reach edge r n ∧ owner n = none

/-- `IsPath edge a l` says that `a :: l` is an `edge`-path. -/
def IsPath (edge : Node → Node → Prop) : Node → List Node → Prop
  | _, [] => True
  | a, b :: l => edge a b ∧ IsPath edge b l

/-- The last node of the path `a :: l`. -/
def lastNode : Node → List Node → Node
  | a, [] => a
  | _, b :: l => lastNode b l

/-- An *escape trace* is a path `a :: l` starting at a root and ending at an
unowned location. -/
def EscapeTrace (roots : Node → Prop) (edge : Node → Node → Prop)
    (owner : Node → Option Owner) (a : Node) (l : List Node) : Prop :=
  roots a ∧ IsPath edge a l ∧ owner (lastNode a l) = none

/-- The engine's counterexample output: some concrete escape trace exists. -/
def HasEscapeTrace (roots : Node → Prop) (edge : Node → Node → Prop)
    (owner : Node → Option Owner) : Prop :=
  ∃ a l, EscapeTrace roots edge owner a l

section

variable {roots : Node → Prop} {edge : Node → Node → Prop} {owner : Node → Option Owner}

/-- Prepending an edge to a reachability path. -/
theorem Reach.head {a b c : Node} (h : edge a b) (hbc : Reach edge b c) :
    Reach edge a c := by
  induction hbc with
  | refl => exact Reach.tail Reach.refl h
  | tail _ hcd ih => exact ih.tail hcd

/-- Anything the engine marks as exposed is genuinely reachable from a root. -/
theorem exists_root_reach_of_flows {n : Node} (h : Flows roots edge n) :
    ∃ r, roots r ∧ Reach edge r n := by
  induction h with
  | root hn => exact ⟨_, hn, Reach.refl⟩
  | step _ he ih =>
      obtain ⟨r, hr, hpath⟩ := ih
      exact ⟨r, hr, hpath.tail he⟩

/-- Everything reachable from a root is marked as exposed by the engine. -/
theorem flows_of_reach {r n : Node} (hr : roots r) (h : Reach edge r n) :
    Flows roots edge n := by
  induction h with
  | refl => exact Flows.root hr
  | tail _ he ih => exact ih.step he

/-- Completeness: any escape the engine reports is a genuine reachable unowned
location. -/
theorem unownedReachable_of_nullEscape
    (h : NullEscape roots edge owner) : UnownedReachable roots edge owner := by
  obtain ⟨n, hn, hnull⟩ := h
  obtain ⟨r, hr, hpath⟩ := exists_root_reach_of_flows hn
  exact ⟨r, n, hr, hpath, hnull⟩

/-- Soundness: if the engine reports no null escape, then no unowned location is
reachable from a root. -/
theorem not_unownedReachable_of_not_nullEscape
    (h : ¬ NullEscape roots edge owner) : ¬ UnownedReachable roots edge owner := by
  rintro ⟨r, n, hr, hpath, hnull⟩
  exact h ⟨n, flows_of_reach hr hpath, hnull⟩

/-- **Main theorem.**  The isolation engine reports a null escape if and only if
the model has an unowned location reachable from a root. -/
theorem null_escape_iff_unowned_reachable :
    NullEscape roots edge owner ↔ UnownedReachable roots edge owner := by
  refine ⟨unownedReachable_of_nullEscape, ?_⟩
  rintro ⟨r, n, hr, hpath, hnull⟩
  exact ⟨n, flows_of_reach hr hpath, hnull⟩

/-! ### Concrete escape traces -/

/-- Any `edge`-path from `a` witnesses reachability of its last node. -/
theorem reach_lastNode : ∀ (l : List Node) (a : Node), IsPath edge a l →
    Reach edge a (lastNode a l)
  | [], _, _ => Reach.refl
  | b :: l, _, h => Reach.head h.1 (reach_lastNode l b h.2)

/-- The last node of a path extended by one node is that node. -/
theorem lastNode_append_singleton :
    ∀ (l : List Node) (a c : Node), lastNode a (l ++ [c]) = c
  | [], _, _ => rfl
  | b :: l, _, c => lastNode_append_singleton l b c

/-- A path may be extended by an edge leaving its last node. -/
theorem isPath_append_singleton : ∀ (l : List Node) (a c : Node), IsPath edge a l →
    edge (lastNode a l) c → IsPath edge a (l ++ [c])
  | [], _, _, _, h => ⟨h, trivial⟩
  | b :: l, _, c, hp, h => ⟨hp.1, isPath_append_singleton l b c hp.2 h⟩

/-- Reachability yields a concrete path with the given endpoints. -/
theorem exists_path_of_reach {a n : Node} (h : Reach edge a n) :
    ∃ l, IsPath edge a l ∧ lastNode a l = n := by
  induction h with
  | refl => exact ⟨[], trivial, rfl⟩
  | @tail b c _ hbc ih =>
      obtain ⟨l, hl, hlast⟩ := ih
      exact ⟨l ++ [c], isPath_append_singleton l a c hl (hlast ▸ hbc),
        lastNode_append_singleton l a c⟩

/-- Every reachable unowned location comes with a concrete escape trace. -/
theorem hasEscapeTrace_of_unownedReachable
    (h : UnownedReachable roots edge owner) : HasEscapeTrace roots edge owner := by
  obtain ⟨r, n, hr, hpath, hnull⟩ := h
  obtain ⟨l, hl, hlast⟩ := exists_path_of_reach hpath
  exact ⟨r, l, hr, hl, hlast ▸ hnull⟩

/-- An escape trace witnesses a reachable unowned location. -/
theorem unownedReachable_of_hasEscapeTrace
    (h : HasEscapeTrace roots edge owner) : UnownedReachable roots edge owner := by
  obtain ⟨a, l, hr, hl, hnull⟩ := h
  exact ⟨a, lastNode a l, hr, reach_lastNode l a hl, hnull⟩

/-- The three notions agree: the engine reports a null escape iff an unowned
location is reachable from a root iff there is a concrete escape trace. -/
theorem null_escape_iff_hasEscapeTrace :
    NullEscape roots edge owner ↔ HasEscapeTrace roots edge owner :=
  ⟨fun h => hasEscapeTrace_of_unownedReachable (unownedReachable_of_nullEscape h),
   fun h => null_escape_iff_unowned_reachable.mpr (unownedReachable_of_hasEscapeTrace h)⟩

end

end Isolation
end PCA

