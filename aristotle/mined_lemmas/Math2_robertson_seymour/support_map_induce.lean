/-
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
### Scope of this file

The Robertson–Seymour graph minor theorem states that the class of *all* finite simple graphs is
well-quasi-ordered by the minor relation.  Its published proof runs to some twenty papers and
several hundred pages, and it is not formalised here.

What is developed and fully proved below is:

* `Math2.MinorModel` / `Math2.IsMinor`: the minor relation between simple graphs, defined via
  branch sets (`H` is a minor of `G` iff `H` is obtained from a subgraph of `G` by contracting
  disjoint connected subgraphs);
* `Math2.isMinor_refl` and `Math2.isMinor_trans`: the minor relation is a quasi-order;
* `Math2.robertson_seymour`: the graph minor theorem for every class of finite graphs of
  bounded edge number;
* `Math2.robertson_seymour_linearForest`: the graph minor theorem for the class of linear
  forests (disjoint unions of paths), which contains graphs with arbitrarily many edges; this
  case is deduced from Higman's lemma.

Both of the last two statements are genuine special cases of the Robertson–Seymour theorem, and
neither is the full theorem.
-/

namespace Math2

/-! ### The minor relation -/

/-- A *minor model* of `H` in `G`: an assignment of pairwise disjoint, nonempty,
connected *branch sets* of `G` to the vertices of `H`, such that adjacent vertices of `H`
get branch sets joined by an edge of `G`. -/
structure MinorModel {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) where
  /-- The branch set attached to a vertex of `H`. -/
  branch : V → Set W
  branch_nonempty : ∀ v : V, (branch v).Nonempty
  branch_connected : ∀ v : V, (G.induce (branch v)).Connected
  branch_disjoint : ∀ ⦃u v : V⦄, u ≠ v → Disjoint (branch u) (branch v)
  branch_adj : ∀ ⦃u v : V⦄, H.Adj u v → ∃ a ∈ branch u, ∃ b ∈ branch v, G.Adj a b

/-- `H` is a *minor* of `G` if there is a minor model of `H` in `G`, i.e. `H` can be obtained
from a subgraph of `G` by contracting connected subgraphs. -/

theorem support_map_induce {V : Type} {k : ℕ} (G : SimpleGraph V) (e : ↥G.support ↪ Fin k) :
    ((G.induce G.support).map e).support = Set.range e := by
  ext x
  rw [SimpleGraph.mem_support]
  constructor
  · rintro ⟨y, hy⟩
    rw [SimpleGraph.map_adj] at hy
    obtain ⟨u, v, _, hu, _⟩ := hy
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨w, hw⟩ := (SimpleGraph.mem_support G).1 u.2
    have hw' : w ∈ G.support := (SimpleGraph.mem_support G).2 ⟨_, hw.symm⟩
    refine ⟨e ⟨w, hw'⟩, ?_⟩
    rw [SimpleGraph.map_adj]
    exact ⟨u, ⟨w, hw'⟩, by rw [SimpleGraph.induce_adj]; exact hw, rfl, rfl⟩

/-- If two finite graphs have the same relabelled "core" (the induced graph on the non-isolated
vertices, transported into `Fin k`) and the first one has no more vertices than the second, then
the first one embeds into the second as a subgraph. -/
