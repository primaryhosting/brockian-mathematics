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
