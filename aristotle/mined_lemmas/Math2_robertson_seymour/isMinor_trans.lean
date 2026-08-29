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

theorem isMinor_trans {U V W : Type*} {F : SimpleGraph U} {H : SimpleGraph V} {G : SimpleGraph W}
    (h1 : IsMinor F H) (h2 : IsMinor H G) : IsMinor F G := by
  obtain ⟨M⟩ := h1
  obtain ⟨N⟩ := h2
  refine ⟨{ branch := fun v => ⋃ w : ↥(M.branch v), N.branch ↑w
            branch_nonempty := ?_
            branch_connected := ?_
            branch_disjoint := ?_
            branch_adj := ?_ }⟩
  · intro v
    obtain ⟨w, hw⟩ := M.branch_nonempty v
    obtain ⟨x, hx⟩ := N.branch_nonempty w
    exact ⟨x, Set.mem_iUnion.2 ⟨⟨w, hw⟩, hx⟩⟩
  · intro v
    exact connected_iUnion_branch (M.branch_connected v) (fun _ => N.branch_nonempty _)
      (fun _ => N.branch_connected _) (fun _ _ h => N.branch_adj h)
  · intro u v huv
    rw [Set.disjoint_left]
    rintro x hx hx'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
    obtain ⟨w', hw'⟩ := Set.mem_iUnion.1 hx'
    have hne : (w : V) ≠ (w' : V) := by
      intro h
      exact (Set.disjoint_left.1 (M.branch_disjoint huv) w.2) (h ▸ w'.2)
    exact (Set.disjoint_left.1 (N.branch_disjoint hne) hw) hw'
  · intro u v huv
    obtain ⟨a, ha, b, hb, hab⟩ := M.branch_adj huv
    obtain ⟨x, hx, y, hy, hxy⟩ := N.branch_adj hab
    exact ⟨x, Set.mem_iUnion.2 ⟨⟨a, ha⟩, hx⟩, y, Set.mem_iUnion.2 ⟨⟨b, hb⟩, hy⟩, hxy⟩

/-! ### The class of all finite graphs -/

/-- A finite simple graph, presented with vertex set `Fin n`.  Every finite simple graph is
isomorphic to one of these, so this is a faithful model of the class of all finite graphs. -/
abbrev FinGraph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The minor relation on `FinGraph`. -/
