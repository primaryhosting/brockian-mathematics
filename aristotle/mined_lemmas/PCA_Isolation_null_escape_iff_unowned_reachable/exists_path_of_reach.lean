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
