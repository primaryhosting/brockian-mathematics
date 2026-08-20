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
