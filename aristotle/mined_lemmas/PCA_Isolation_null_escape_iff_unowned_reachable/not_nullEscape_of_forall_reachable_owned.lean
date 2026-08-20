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

theorem not_nullEscape_of_forall_reachable_owned (I : Isolate α)
    (h : ∀ n, Reaches I I.root n → n ∈ I.owned) : ¬ NullEscape I := by
  rw [null_escape_iff_unowned_reachable]
  rintro ⟨n, hreach, hn⟩
  exact hn (h n hreach)

/-- **Completeness.** If some unowned object is reachable, the engine can exhibit an escape
trace. -/
