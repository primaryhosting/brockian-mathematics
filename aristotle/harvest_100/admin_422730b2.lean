import Mathlib
/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The full Robertson–Seymour graph minor theorem states that *all* finite graphs are
well-quasi-ordered by the minor relation.  Its only known proof is the Graph Minors series
of Robertson and Seymour, spanning hundreds of pages, and it is not formalized here.

What is developed and proved below, axiom-free, is:

* the minor relation on finite simple graphs, via branch-set minor models
  (`Math2.MinorModel`, `Math2.IsMinor`);
* `Math2.isMinor_of_embedding`: a subgraph embedding yields a minor;
* `Math2.robertson_seymour`: well-quasi-ordering by the minor relation for the (infinite)
  class of graphs with at most `k` non-isolated vertices;
* the corollaries `Math2.robertson_seymour_bounded_order` (at most `k` vertices) and
  `Math2.robertson_seymour_bounded_size` (at most `k` edges), in both cases with
  arbitrarily many isolated vertices allowed.
-/

open scoped Classical

namespace Math2

/-- A finite simple graph, presented as a simple graph on `Fin n`. -/
structure FinGraph where
  n : ℕ
  G : SimpleGraph (Fin n)

/-- A *minor model* of `H` inside `K`: a family of pairwise disjoint, nonempty, connected
branch sets of `K`, one for each vertex of `H`, such that adjacent vertices of `H` have
branch sets joined by an edge of `K`. -/
structure MinorModel (H K : FinGraph) where
  B : Fin H.n → Set (Fin K.n)
  nonempty' : ∀ h, (B h).Nonempty
  disj : ∀ h h', h ≠ h' → Disjoint (B h) (B h')
  conn : ∀ h, (K.G.induce (B h)).Connected
  edge : ∀ h h', H.G.Adj h h' → ∃ a ∈ B h, ∃ b ∈ B h', K.G.Adj a b

/-- `H` is a minor of `K`. -/
def IsMinor (H K : FinGraph) : Prop := Nonempty (MinorModel H K)

/-- If `H` embeds into `K` as a subgraph, then `H` is a minor of `K`. -/
theorem isMinor_of_embedding (H K : FinGraph) (f : Fin H.n → Fin K.n)
    (hf : Function.Injective f) (hadj : ∀ a b, H.G.Adj a b → K.G.Adj (f a) (f b)) :
    IsMinor H K := by
  refine ⟨{ B := fun h => {f h}, nonempty' := fun h => ⟨f h, rfl⟩,
            disj := ?_, conn := ?_, edge := ?_ }⟩
  · intro h h' hne
    exact Set.disjoint_singleton.mpr (fun hc => hne (hf hc))
  · intro h
    have : Nonempty ({f h} : Set (Fin K.n)) := ⟨⟨f h, rfl⟩⟩
    exact SimpleGraph.Connected.of_subsingleton
  · intro h h' hh
    exact ⟨f h, rfl, f h', rfl, hadj _ _ hh⟩

/-- Any graph is a minor of itself. -/
theorem isMinor_refl (X : FinGraph) : IsMinor X X :=
  isMinor_of_embedding X X id Function.injective_id (fun _ _ h => h)

/-- A minor has at most as many vertices as the host graph; in particular the minor
relation is not a trivial relation. -/
theorem IsMinor.order_le {H K : FinGraph} (h : IsMinor H K) : H.n ≤ K.n := by
  classical
  obtain ⟨m⟩ := h
  have hinj : Function.Injective (fun v : Fin H.n => (m.nonempty' v).choose) := by
    intro a b hab
    by_contra hne
    have hd := m.disj a b hne
    have ha := (m.nonempty' a).choose_spec
    have hb := (m.nonempty' b).choose_spec
    simp only at hab
    rw [hab] at ha
    exact Set.disjoint_left.mp hd ha hb
  simpa using Fintype.card_le_of_injective _ hinj

/-- The set of non-isolated vertices of a graph. -/
noncomputable def FinGraph.support (X : FinGraph) : Finset (Fin X.n) :=
  Finset.univ.filter (fun v => ∃ w, X.G.Adj v w)

theorem FinGraph.mem_support {X : FinGraph} {a b : Fin X.n} (h : X.G.Adj a b) :
    a ∈ X.support := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, h⟩⟩

/-- A graph has at most twice as many non-isolated vertices as edges. -/
theorem FinGraph.card_support_le (X : FinGraph) :
    X.support.card ≤ 2 * X.G.edgeSet.ncard := by
  classical
  set g : Fin X.n → Sym2 (Fin X.n) :=
    fun v => if h : ∃ w, X.G.Adj v w then s(v, h.choose) else s(v, v) with hg
  have hmem : ∀ v ∈ X.support, g v ∈ X.G.edgeSet ∧ v ∈ g v := by
    intro v hv
    have h : ∃ w, X.G.Adj v w := (Finset.mem_filter.mp hv).2
    simp only [hg, dif_pos h]
    exact ⟨h.choose_spec, Sym2.mem_mk_left _ _⟩
  have h1 : X.support.card ≤ 2 * (Finset.image g X.support).card := by
    refine Finset.card_le_mul_card_image _ 2 ?_
    intro b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hb
    induction (g a₀) using Sym2.ind with
    | _ x y =>
      refine le_trans (Finset.card_le_card (t := ({x, y} : Finset (Fin X.n))) ?_) ?_
      · intro c hc
        simp only [Finset.mem_filter] at hc
        have : c ∈ s(x, y) := hc.2 ▸ (hmem c hc.1).2
        simpa [Sym2.mem_iff] using this
      · exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hfin : X.G.edgeSet.Finite := Set.toFinite _
  have h2 : (Finset.image g X.support).card ≤ X.G.edgeSet.ncard := by
    have hsub : (Finset.image g X.support) ⊆ hfin.toFinset := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      simpa using (hmem a ha).1
    calc (Finset.image g X.support).card ≤ hfin.toFinset.card := Finset.card_le_card hsub
      _ = X.G.edgeSet.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
  omega

/-- The position of a non-isolated vertex in the increasing enumeration of the support. -/
noncomputable def FinGraph.rank (X : FinGraph) : X.support → Fin X.support.card :=
  (X.support.orderIsoOfFin rfl).symm

/-- The isomorphism type of the graph induced on the support, recorded as a relation on
`Fin k` via the rank function. This is a *finite* invariant when the support has at most
`k` elements. -/
noncomputable def FinGraph.pat (k : ℕ) (X : FinGraph) : Fin k → Fin k → Prop :=
  fun a b => ∃ v w : X.support, X.G.Adj v w ∧
    ((X.rank v : ℕ) = (a : ℕ)) ∧ ((X.rank w : ℕ) = (b : ℕ))

/-- Two graphs with the same support size and the same pattern, the first having no more
vertices than the second: there is a subgraph embedding of the first into the second. -/
theorem exists_embedding_of_pat_eq (k : ℕ) (X Y : FinGraph)
    (hcard : X.support.card = Y.support.card)
    (hpat : FinGraph.pat k X = FinGraph.pat k Y)
    (hkX : X.support.card ≤ k)
    (hn : X.n ≤ Y.n) :
    ∃ f : Fin X.n → Fin Y.n, Function.Injective f ∧
      ∀ a b, X.G.Adj a b → Y.G.Adj (f a) (f b) := by
  have hcompl : Fintype.card ((X.supportᶜ : Finset (Fin X.n))) ≤
      Fintype.card ((Y.supportᶜ : Finset (Fin Y.n))) := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcompl
  set eY : Fin Y.support.card ≃o Y.support := Y.support.orderIsoOfFin rfl with heY
  set fs : X.support → Y.support := fun v => eY (Fin.cast hcard (X.rank v)) with hfs
  have hfs_inj : Function.Injective fs := by
    intro a b hab
    simp only [hfs, EmbeddingLike.apply_eq_iff_eq] at hab
    have : X.rank a = X.rank b := by
      apply Fin.ext; simpa [Fin.ext_iff] using hab
    have := congrArg (X.support.orderIsoOfFin rfl) this
    simpa [FinGraph.rank] using this
  refine ⟨fun v => if hv : v ∈ X.support then (fs ⟨v, hv⟩ : Fin Y.n)
      else (e ⟨v, Finset.mem_compl.mpr hv⟩ : Fin Y.n), ?_, ?_⟩
  · intro a b hab
    by_cases ha : a ∈ X.support <;> by_cases hb : b ∈ X.support <;>
      simp only [ha, hb, dif_pos, dif_neg, not_false_iff] at hab
    · exact congrArg Subtype.val (hfs_inj (Subtype.ext hab))
    · exfalso
      have h1 : (fs ⟨a, ha⟩ : Fin Y.n) ∈ Y.support := (fs ⟨a, ha⟩).2
      have h2 : (e ⟨b, Finset.mem_compl.mpr hb⟩ : Fin Y.n) ∈ Y.supportᶜ :=
        (e ⟨b, Finset.mem_compl.mpr hb⟩).2
      rw [hab] at h1
      exact (Finset.mem_compl.mp h2) h1
    · exfalso
      have h1 : (fs ⟨b, hb⟩ : Fin Y.n) ∈ Y.support := (fs ⟨b, hb⟩).2
      have h2 : (e ⟨a, Finset.mem_compl.mpr ha⟩ : Fin Y.n) ∈ Y.supportᶜ :=
        (e ⟨a, Finset.mem_compl.mpr ha⟩).2
      rw [← hab] at h1
      exact (Finset.mem_compl.mp h2) h1
    · exact congrArg Subtype.val (e.injective (Subtype.ext hab))
  · intro a b hab
    have ha : a ∈ X.support := FinGraph.mem_support hab
    have hb : b ∈ X.support := FinGraph.mem_support hab.symm
    simp only [ha, hb, dif_pos]
    set A : Fin k := ⟨(X.rank ⟨a, ha⟩ : ℕ), lt_of_lt_of_le (X.rank ⟨a, ha⟩).isLt hkX⟩ with hA
    set B : Fin k := ⟨(X.rank ⟨b, hb⟩ : ℕ), lt_of_lt_of_le (X.rank ⟨b, hb⟩).isLt hkX⟩ with hB
    have hX : FinGraph.pat k X A B := ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, rfl, rfl⟩
    rw [hpat] at hX
    obtain ⟨v, w, hvw, hv, hw⟩ := hX
    have key : ∀ (u : X.support) (z : Y.support),
        ((Y.rank z : ℕ) = (X.rank u : ℕ)) → fs u = z := by
      intro u z hz
      have : Y.rank z = Fin.cast hcard (X.rank u) := Fin.ext (by simpa using hz)
      have := congrArg eY this
      simpa [FinGraph.rank, heY, hfs] using this.symm
    have hav : fs ⟨a, ha⟩ = v := key _ _ (by simpa [hA] using hv)
    have hbw : fs ⟨b, hb⟩ = w := key _ _ (by simpa [hB] using hw)
    rw [hav, hbw]
    exact hvw

/-- Pigeonhole: an `ℕ`-indexed family with values in a finite type, together with an
auxiliary `ℕ`-valued weight, has two indices `i < j` with equal values and increasing
weight. -/
theorem exists_lt_eq_and_le {α : Type} [Finite α] (f : ℕ → α) (g : ℕ → ℕ) :
    ∃ i j, i < j ∧ f i = f j ∧ g i ≤ g j := by
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hT : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  have hs : (g '' (f ⁻¹' {y})).Nonempty := hT.nonempty.image g
  obtain ⟨i, hi, hgi⟩ := Nat.sInf_mem hs
  obtain ⟨j, hj, hij⟩ := hT.exists_gt i
  refine ⟨i, j, hij, ?_, ?_⟩
  · have h1 : f i = y := hi
    have h2 : f j = y := hj
    rw [h1, h2]
  · have hmem : g j ∈ (g '' (f ⁻¹' {y})) := ⟨j, hj, rfl⟩
    calc g i = sInf (g '' (f ⁻¹' {y})) := hgi
      _ ≤ g j := Nat.sInf_le hmem

/--
**Robertson–Seymour (bounded-support case).**

Graphs with at most `k` non-isolated vertices are well-quasi-ordered by the minor relation:
in any infinite sequence of such graphs there are indices `i < j` with `Gs i` a minor of
`Gs j`.

Note: this is the bounded-support special case of the Robertson–Seymour graph minor
theorem, not the full theorem (whose known proof spans hundreds of pages).  The class
covered here is nonetheless infinite: for every `k` it contains all graphs with at most
`k` vertices (see `robertson_seymour_bounded_order`) and all graphs with at most `k` edges
(see `robertson_seymour_bounded_size`), each with arbitrarily many isolated vertices added.
-/
theorem robertson_seymour (k : ℕ) (Gs : ℕ → FinGraph)
    (hk : ∀ i, (Gs i).support.card ≤ k) :
    ∃ i j, i < j ∧ IsMinor (Gs i) (Gs j) := by
  obtain ⟨i, j, hij, hfe, hle⟩ :=
    exists_lt_eq_and_le (α := Fin (k + 1) × (Fin k → Fin k → Prop))
      (fun i => (⟨(Gs i).support.card, Nat.lt_succ_of_le (hk i)⟩, FinGraph.pat k (Gs i)))
      (fun i => (Gs i).n)
  have hcard : (Gs i).support.card = (Gs j).support.card := by
    have := congrArg Prod.fst hfe
    simpa [Fin.ext_iff] using this
  have hpat : FinGraph.pat k (Gs i) = FinGraph.pat k (Gs j) := congrArg Prod.snd hfe
  obtain ⟨f, hf, hadj⟩ := exists_embedding_of_pat_eq k (Gs i) (Gs j) hcard hpat (hk i) hle
  exact ⟨i, j, hij, isMinor_of_embedding _ _ f hf hadj⟩

/-- Graphs with at most `k` vertices are well-quasi-ordered by the minor relation. -/
theorem robertson_seymour_bounded_order (k : ℕ) (Gs : ℕ → FinGraph)
    (hk : ∀ i, (Gs i).n ≤ k) :
    ∃ i j, i < j ∧ IsMinor (Gs i) (Gs j) := by
  refine robertson_seymour k Gs (fun i => ?_)
  calc (Gs i).support.card ≤ (Finset.univ : Finset (Fin (Gs i).n)).card :=
        Finset.card_le_univ _
    _ = (Gs i).n := by simp
    _ ≤ k := hk i

/-- Graphs with at most `k` edges are well-quasi-ordered by the minor relation. -/
theorem robertson_seymour_bounded_size (k : ℕ) (Gs : ℕ → FinGraph)
    (hk : ∀ i, (Gs i).G.edgeSet.ncard ≤ k) :
    ∃ i j, i < j ∧ IsMinor (Gs i) (Gs j) := by
  refine robertson_seymour (2 * k) Gs (fun i => ?_)
  exact le_trans (FinGraph.card_support_le (Gs i)) (Nat.mul_le_mul_left 2 (hk i))

end Math2

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

