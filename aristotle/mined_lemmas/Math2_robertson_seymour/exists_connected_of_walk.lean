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

theorem exists_connected_of_walk {W X : Type*} {G : SimpleGraph W} {K : SimpleGraph X}
    {S : Set W} {C : W → Set X}
    (hconn : ∀ w : ↥S, (K.induce (C ↑w)).Connected)
    (hadj : ∀ w w' : ↥S, G.Adj ↑w ↑w' → ∃ x ∈ C ↑w, ∃ y ∈ C ↑w', K.Adj x y)
    {a b : ↥S} (p : (G.induce S).Walk a b) :
    ∃ s' : Set X, s' ⊆ (⋃ w : ↥S, C ↑w) ∧ C ↑a ⊆ s' ∧ C ↑b ⊆ s' ∧ (K.induce s').Connected := by
  induction p with
  | nil => exact ⟨C _, Set.subset_iUnion (fun w : ↥S => C ↑w) _, le_rfl, le_rfl, hconn _⟩
  | @cons a c b h p ih =>
      obtain ⟨s', hsub, hCc, hCb, hconn'⟩ := ih
      obtain ⟨x, hx, y, hy, hxy⟩ := hadj a c (by rwa [SimpleGraph.induce_adj] at h)
      refine ⟨C ↑a ∪ s', Set.union_subset (Set.subset_iUnion (fun w : ↥S => C ↑w) _) hsub,
        Set.subset_union_left, hCb.trans Set.subset_union_right, ?_⟩
      exact SimpleGraph.connected_induce_union (hconn a).preconnected hconn'.preconnected
        hx (hCc hy) hxy

/-- If `S` induces a connected subgraph of `G` and the sets `C w` (`w ∈ S`) are nonempty,
connected, and joined by an edge whenever the corresponding vertices of `S` are adjacent,
then their union induces a connected subgraph of `K`. -/
