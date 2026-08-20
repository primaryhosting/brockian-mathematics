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

theorem chainFrom_append_edge {e : V → V → Prop} (l : List V) :
    ∀ (a c : V), chainFrom e a l → e (lastOf a l) c → chainFrom e a (l ++ [c]) := by
  induction l with
  | nil => intro _ _ _ hc; exact ⟨hc, trivial⟩
  | cons b l ih => intro _ c h hc; exact ⟨h.1, ih b c h.2 hc⟩

/-- The last object of an extended trace is the newly appended one. -/
