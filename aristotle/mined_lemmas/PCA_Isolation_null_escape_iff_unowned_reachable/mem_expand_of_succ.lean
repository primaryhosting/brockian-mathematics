import Mathlib

/-!
# A formal model of a pointer-capability isolation engine

This file develops a small but complete formal model of the *isolation engine* used by a
pointer-capability analysis (`PCA`).

The model consists of

* a finite object graph `Graph V`, given by a successor (reference) function `succ`,
  an ownership predicate `owned` (`false` means the object is *unowned*, i.e. outside the
  isolation domain) and a finite set of `roots` (the entry points of the domain);
* an *inductive* specification of which objects are reachable from the roots (`Reachable`);
* an *executable* fixpoint engine (`closure`, `reachSet`, `escapeSet`) that computes the
  reachable set by saturation and reports the set of escaping objects.

The main results are

* `PCA.Isolation.mem_reachSet_iff` : the engine's reachable set is exactly the inductively
  specified reachable set (soundness and completeness of the reachability engine);
* `PCA.Isolation.mem_escapeSet_iff` : an object is reported as escaping iff it is reachable
  and unowned;
* `PCA.Isolation.null_escape_iff_unowned_reachable` : the engine reports no escape iff no
  unowned object is reachable from the roots.
-/

namespace PCA.Isolation

/-- A finite object graph together with an ownership predicate and a set of roots. -/
structure Graph (V : Type*) where
  /-- The objects directly referenced by an object. -/
  succ : V → Finset V
  /-- `owned v = true` means `v` belongs to the isolation domain. -/
  owned : V → Bool
  /-- Entry points of the isolation domain. -/
  roots : Finset V

variable {V : Type*} [DecidableEq V]

/-- Specification: the objects reachable from the roots by following references. -/
inductive Reachable (g : Graph V) : V → Prop
  | root {v : V} (hv : v ∈ g.roots) : Reachable g v
  | step {u v : V} (hu : Reachable g u) (huv : v ∈ g.succ u) : Reachable g v

/-- One saturation step of the engine: add all successors of the current set. -/

lemma mem_expand_of_succ {g : Graph V} {s : Finset V} {u v : V} (hu : u ∈ s)
    (huv : v ∈ g.succ u) : v ∈ expand g s :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hu, huv⟩)

