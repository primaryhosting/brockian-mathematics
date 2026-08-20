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

theorem Reaches.head {e : V → V → Prop} {a b c : V} (hab : e a b) (h : Reaches e b c) :
    Reaches e a c := by
  induction h with
  | refl => exact Reaches.tail (Reaches.refl a) hab
  | tail _ hcd ih => exact Reaches.tail ih hcd

/-- Soundness of traces: following a concrete trace witnesses reachability of its last
object. (Mathlib analogue: `List.relationReflTransGen_of_exists_isChain`.) -/
