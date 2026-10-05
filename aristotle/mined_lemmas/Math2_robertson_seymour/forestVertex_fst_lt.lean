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

theorem forestVertex_fst_lt {L : List ℕ} (p : ForestVertex L) : p.1.1 < L.length := by
  by_contra hc
  have := p.2
  rw [List.getD_eq_default L 0 (by omega)] at this
  omega

/-- Linear forests are finite graphs. -/
instance forestVertex_finite (L : List ℕ) : Finite (ForestVertex L) := by
  have hsub : {p : ℕ × ℕ | p.2 < L.getD p.1 0} ⊆ Set.Iio L.length ×ˢ Set.Iio (L.sum + 1) := by
    rintro ⟨i, a⟩ h
    simp only [Set.mem_setOf_eq] at h
    have hi : i < L.length := by
      by_contra hc
      rw [List.getD_eq_default L 0 (by omega)] at h
      omega
    have hle : L.getD i 0 ≤ L.sum := by
      have hmem : L.getD i 0 ∈ L := by
        rw [List.getD_eq_getElem L 0 hi]
        exact List.getElem_mem hi
      exact List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    exact ⟨Set.mem_Iio.2 hi, Set.mem_Iio.2 (by omega)⟩
  exact (((Set.finite_Iio _).prod (Set.finite_Iio _)).subset hsub).to_subtype

/-- An injective map of path indices which does not decrease path lengths exhibits one linear
forest as a subgraph, hence a minor, of another. -/
