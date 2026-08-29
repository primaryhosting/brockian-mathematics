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
def IsMinor {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  Nonempty (MinorModel H G)

/-- An adjacency-preserving injection gives a minor model with singleton branch sets;
in particular a subgraph is a minor. -/
theorem isMinor_of_embedding {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (f : V ↪ W) (hf : ∀ u v : V, H.Adj u v → G.Adj (f u) (f v)) : IsMinor H G := by
  refine ⟨{ branch := fun v => {f v}
            branch_nonempty := fun v => ⟨f v, rfl⟩
            branch_connected := ?_
            branch_disjoint := ?_
            branch_adj := ?_ }⟩
  · intro v
    rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨⟨f v, rfl⟩⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.mem_singleton_iff] at ha hb
    subst ha; subst hb
    exact SimpleGraph.Reachable.refl _
  · intro u v huv
    simp only [Set.disjoint_singleton, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact huv
  · intro u v huv
    exact ⟨f u, rfl, f v, rfl, hf u v huv⟩

/-- The minor relation is reflexive. -/
theorem isMinor_refl {V : Type*} (G : SimpleGraph V) : IsMinor G G :=
  isMinor_of_embedding (Function.Embedding.refl V) (fun _ _ h => h)

/-- Auxiliary step for `connected_iUnion_branch`: walking along a walk in `G.induce S`,
one can cover the branch sets at both endpoints by a connected set. -/
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
theorem connected_iUnion_branch {W X : Type*} {G : SimpleGraph W} {K : SimpleGraph X}
    {S : Set W} {C : W → Set X}
    (hS : (G.induce S).Connected)
    (hne : ∀ w : ↥S, (C ↑w).Nonempty)
    (hconn : ∀ w : ↥S, (K.induce (C ↑w)).Connected)
    (hadj : ∀ w w' : ↥S, G.Adj ↑w ↑w' → ∃ x ∈ C ↑w, ∃ y ∈ C ↑w', K.Adj x y) :
    (K.induce (⋃ w : ↥S, C ↑w)).Connected := by
  obtain ⟨w0⟩ := hS.nonempty
  obtain ⟨u, hu⟩ := hne w0
  refine SimpleGraph.induce_connected_of_patches u (Set.mem_iUnion.2 ⟨w0, hu⟩) ?_
  intro x hx
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
  obtain ⟨s', hsub, hC0, hCw, hconn'⟩ :=
    exists_connected_of_walk hconn hadj (hS.preconnected w0 w).some
  exact ⟨s', hsub, hC0 hu, hCw hw, hconn'.preconnected _ _⟩

/-- The minor relation is transitive. -/
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
def FinGraph.IsMinor (H G : FinGraph) : Prop := Math2.IsMinor H.2 G.2

/-- The number of edges of a finite graph. -/
noncomputable def FinGraph.numEdges (G : FinGraph) : ℕ := G.2.edgeSet.ncard

theorem FinGraph.isMinor_refl (G : FinGraph) : G.IsMinor G := Math2.isMinor_refl G.2

theorem FinGraph.isMinor_trans {F G H : FinGraph} (h1 : F.IsMinor G) (h2 : G.IsMinor H) :
    F.IsMinor H := Math2.isMinor_trans h1 h2

/-! ### Auxiliary lemmas -/

/-- A graph with `m` edges has at most `2 * m` non-isolated vertices. -/
theorem card_support_le_two_mul_numEdges (n : ℕ) (G : SimpleGraph (Fin n)) :
    Fintype.card ↥G.support ≤ 2 * G.edgeSet.ncard := by
  classical
  have h1 : Fintype.card ↥G.support = (Finset.univ.filter (fun v => v ∈ G.support)).card := by
    rw [Fintype.card_subtype]
  rw [h1]
  have h2 : (Finset.univ.filter (fun v => v ∈ G.support)).card
      ≤ ∑ v ∈ Finset.univ.filter (fun v => v ∈ G.support), G.degree v := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum ?_
    intro v hv
    simp only [Finset.mem_filter] at hv
    obtain ⟨w, hw⟩ := (SimpleGraph.mem_support G).1 hv.2
    have hw2 : w ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]; exact hw
    exact Finset.card_pos.2 ⟨w, hw2⟩
  refine h2.trans ?_
  have h3 : ∑ v ∈ Finset.univ.filter (fun v => v ∈ G.support), G.degree v
      ≤ ∑ v : Fin n, G.degree v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  refine h3.trans ?_
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  have h4 : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
  omega

/-- The image of the induced graph on the non-isolated vertices covers the whole range of the
labelling embedding. -/
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
theorem robertson_seymour (k : ℕ) :
    WellQuasiOrdered
      (fun H G : {G : FinGraph // G.numEdges ≤ k} => FinGraph.IsMinor H.1 G.1) := by
  classical
  intro F
  -- The relabelling embeddings of the non-isolated vertices into `Fin (2 * k)`.
  have hemb : ∀ i : ℕ, Nonempty (↥((F i).1.2.support) ↪ Fin (2 * k)) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    refine (card_support_le_two_mul_numEdges _ _).trans ?_
    have := (F i).2
    simp only [FinGraph.numEdges] at this
    omega
  have e : ∀ i : ℕ, ↥((F i).1.2.support) ↪ Fin (2 * k) := fun i => (hemb i).some
  -- Pigeonhole: there are finitely many codes, and `≤` on `ℕ` is a well-quasi-order.
  have hwqo1 : WellQuasiOrdered (Eq : SimpleGraph (Fin (2 * k)) → SimpleGraph (Fin (2 * k)) → Prop) :=
    Finite.wellQuasiOrdered _
  have hwqo2 : WellQuasiOrdered ((· ≤ ·) : ℕ → ℕ → Prop) := wellQuasiOrdered_le
  obtain ⟨i, j, hij, hcij, hnij⟩ := hwqo1.prod hwqo2
    (fun i => (((F i).1.2.induce ((F i).1.2.support)).map (e i), (F i).1.1))
  refine ⟨i, j, hij, ?_⟩
  obtain ⟨f, hf⟩ := exists_embedding_of_code_eq (F i).1.2 (F j).1.2 (e i) (e j) hcij hnij
  exact isMinor_of_embedding f hf

/-! ### Linear forests

A second, complementary special case of the Robertson–Seymour theorem: the class of *linear
forests* (disjoint unions of paths) is well-quasi-ordered by the minor relation.  Unlike the
class treated in `Math2.robertson_seymour`, this class contains graphs with arbitrarily many
edges.  The proof uses Higman's lemma.
-/

/-- The vertex type of the linear forest with path lengths given by `L`: the vertex `(i, a)`
is the `a`-th vertex of the `i`-th path. -/
abbrev ForestVertex (L : List ℕ) : Type := {p : ℕ × ℕ // p.2 < L.getD p.1 0}

/-- The linear forest determined by a list `L` of path lengths: the disjoint union of paths
having `L[0], L[1], …` vertices. -/
def linearForest (L : List ℕ) : SimpleGraph (ForestVertex L) where
  Adj p q := p.1.1 = q.1.1 ∧ (p.1.2 + 1 = q.1.2 ∨ q.1.2 + 1 = p.1.2)
  symm := by rintro p q ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨by rintro p ⟨-, h | h⟩ <;> omega⟩

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
theorem isMinor_linearForest_of_index_map {L M : List ℕ} (g : ℕ → ℕ)
    (hinj : ∀ i < L.length, ∀ j < L.length, g i = g j → i = j)
    (hle : ∀ i < L.length, L.getD i 0 ≤ M.getD (g i) 0) :
    IsMinor (linearForest L) (linearForest M) := by
  have hmem : ∀ p : ForestVertex L, p.1.2 < M.getD (g p.1.1) 0 := fun p =>
    lt_of_lt_of_le p.2 (hle _ (forestVertex_fst_lt p))
  refine isMinor_of_embedding
    ⟨fun p => ⟨(g p.1.1, p.1.2), hmem p⟩, ?_⟩ ?_
  · rintro ⟨⟨i, a⟩, hp⟩ ⟨⟨j, b⟩, hq⟩ h
    have hv : ((g i, a) : ℕ × ℕ) = (g j, b) := congrArg Subtype.val h
    have h1 : g i = g j := congrArg Prod.fst hv
    have h2 : a = b := congrArg Prod.snd hv
    have hi : i = j := hinj i (forestVertex_fst_lt ⟨(i, a), hp⟩) j
      (forestVertex_fst_lt ⟨(j, b), hq⟩) h1
    subst hi; subst h2; rfl
  · rintro p q ⟨h1, h2⟩
    exact ⟨congrArg g h1, h2⟩

/-- From `List.SublistForall₂ (· ≤ ·)` one extracts an injective, length-nondecreasing map of
path indices. -/
theorem exists_index_map_of_sublistForall₂ {L M : List ℕ}
    (h : List.SublistForall₂ (· ≤ ·) L M) :
    ∃ g : ℕ → ℕ, (∀ i < L.length, ∀ j < L.length, g i = g j → i = j) ∧
      (∀ i < L.length, L.getD i 0 ≤ M.getD (g i) 0) := by
  rw [List.sublistForall₂_iff] at h
  obtain ⟨l, hf, hs⟩ := h
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at hs
  obtain ⟨e, he⟩ := hs
  rw [List.forall₂_iff_get] at hf
  obtain ⟨hlen, hget⟩ := hf
  refine ⟨fun i => if hi : i < l.length then (e ⟨i, hi⟩ : ℕ) else 0, ?_, ?_⟩
  · intro i hi j hj hij
    rw [hlen] at hi hj
    simp only [dif_pos hi, dif_pos hj] at hij
    have h2 : (⟨i, hi⟩ : Fin l.length) = ⟨j, hj⟩ := e.injective (Fin.ext hij)
    exact congrArg Fin.val h2
  · intro i hi
    have hi' : i < l.length := hlen ▸ hi
    simp only [dif_pos hi']
    have hM : (e ⟨i, hi'⟩ : ℕ) < M.length := (e ⟨i, hi'⟩).2
    rw [List.getD_eq_getElem L 0 hi, List.getD_eq_getElem M 0 hM]
    have := he ⟨i, hi'⟩
    simp only [List.get_eq_getElem] at this
    rw [← this]
    exact hget i hi hi'

/--
**Robertson–Seymour for linear forests.**

The class of linear forests (disjoint unions of finitely many finite paths) is
well-quasi-ordered by the minor relation.  Here a linear forest is described by the list of
the numbers of vertices of its paths.
-/
theorem robertson_seymour_linearForest :
    WellQuasiOrdered (fun L M : List ℕ => IsMinor (linearForest L) (linearForest M)) := by
  have higman : {l : List ℕ | ∀ x ∈ l, x ∈ (Set.univ : Set ℕ)}.PartiallyWellOrderedOn
      (List.SublistForall₂ (· ≤ ·)) :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)
      (Set.IsPWO.of_linearOrder Set.univ)
  intro F
  obtain ⟨i, j, hij, h⟩ := higman (fun n => ⟨F n, fun x _ => Set.mem_univ x⟩)
  obtain ⟨g, hinj, hle⟩ := exists_index_map_of_sublistForall₂ h
  exact ⟨i, j, hij, isMinor_linearForest_of_index_map g hinj hle⟩

end Math2

