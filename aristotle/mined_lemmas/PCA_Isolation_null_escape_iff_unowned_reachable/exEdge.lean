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

def exEdge : Obj → Obj → Prop
  | .root, .child => True
  | .child, .orphan => True
  | _, _ => False

/-- A heap in which the unowned object `orphan` is reachable. -/
