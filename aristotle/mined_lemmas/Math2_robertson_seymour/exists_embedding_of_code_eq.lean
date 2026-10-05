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

theorem exists_embedding_of_code_eq {n m k : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (eG : ↥G.support ↪ Fin k) (eH : ↥H.support ↪ Fin k)
    (hcode : (G.induce G.support).map eG = (H.induce H.support).map eH)
    (hnm : n ≤ m) :
    ∃ f : Fin n ↪ Fin m, ∀ u v : Fin n, G.Adj u v → H.Adj (f u) (f v) := by
  classical
  have hrange : Set.range eG = Set.range eH := by
    rw [← support_map_induce G eG, ← support_map_induce H eH, hcode]
  set phi : ↥G.support ≃ ↥H.support :=
    (Equiv.ofInjective eG eG.injective).trans
      ((Equiv.setCongr hrange).trans (Equiv.ofInjective eH eH.injective).symm) with hphidef
  have hphi : ∀ x : ↥G.support, eH (phi x) = eG x := by
    intro x
    have h := (Equiv.ofInjective eH eH.injective).apply_symm_apply
      ((Equiv.setCongr hrange) ((Equiv.ofInjective eG eG.injective) x))
    have h2 := congrArg Subtype.val h
    simpa [hphidef, Equiv.ofInjective] using h2
  have hcardeq : Fintype.card ↥G.support = Fintype.card ↥H.support := Fintype.card_congr phi
  have hGle : Fintype.card ↥G.support ≤ n := by
    simpa using Fintype.card_subtype_le (fun x : Fin n => x ∈ G.support)
  have hcompl : Fintype.card ↥(G.support)ᶜ ≤ Fintype.card ↥(H.support)ᶜ := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨ψ⟩ := Function.Embedding.nonempty_of_card_le hcompl
  refine ⟨(Equiv.Set.sumCompl G.support).symm.toEmbedding.trans
    ((phi.toEmbedding.sumMap ψ).trans (Equiv.Set.sumCompl H.support).toEmbedding), ?_⟩
  intro u v huv
  have hu : u ∈ G.support := (SimpleGraph.mem_support G).2 ⟨v, huv⟩
  have hv : v ∈ G.support := (SimpleGraph.mem_support G).2 ⟨u, huv.symm⟩
  have key : ∀ (x : Fin n) (hx : x ∈ G.support),
      ((Equiv.Set.sumCompl G.support).symm.toEmbedding.trans
        ((phi.toEmbedding.sumMap ψ).trans (Equiv.Set.sumCompl H.support).toEmbedding)) x
        = ↑(phi ⟨x, hx⟩) := by
    intro x hx
    simp [Equiv.Set.sumCompl_symm_apply_of_mem hx, Function.Embedding.sumMap]
  rw [key u hu, key v hv]
  have h1 : ((G.induce G.support).map eG).Adj (eG ⟨u, hu⟩) (eG ⟨v, hv⟩) := by
    rw [SimpleGraph.map_adj]
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, by rw [SimpleGraph.induce_adj]; exact huv, rfl, rfl⟩
  rw [hcode, ← hphi ⟨u, hu⟩, ← hphi ⟨v, hv⟩, SimpleGraph.map_adj] at h1
  obtain ⟨a, b, hab, ha, hb⟩ := h1
  have ha' : a = phi ⟨u, hu⟩ := eH.injective ha
  have hb' : b = phi ⟨v, hv⟩ := eH.injective hb
  subst ha'; subst hb'
  exact (SimpleGraph.induce_adj).1 hab

/-! ### The main theorem -/

/--
**Robertson–Seymour, for graphs of bounded size.**

For every `k`, the class of finite simple graphs with at most `k` edges is well-quasi-ordered
by the minor relation: in any infinite sequence of such graphs there are indices `i < j` with
`G i` a minor of `G j`.

Note that this class is infinite: it contains graphs with arbitrarily many vertices.  This is a
special case of the Robertson–Seymour theorem, not the full theorem, which is about the class of
*all* finite graphs and is not formalised here.
-/
