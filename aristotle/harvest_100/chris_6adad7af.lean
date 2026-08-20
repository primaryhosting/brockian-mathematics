/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Finset

namespace Math

/-!
## Combinatorial setting

A triangulation of an `m`-dimensional simplex whose vertices (of the big simplex) are
labelled by a finite set `I` of labels (`I.card = m + 1`) is described combinatorially by:

* a type `V` of vertices of the triangulation;
* a *carrier* map `car : V → Finset ι`, sending a vertex `v` to the set of labels spanning
  the smallest face of the big simplex containing `v` (the support of the barycentric
  coordinates of `v`);
* a finite family `cells : Finset (Finset V)` of maximal cells, each with `m + 1` vertices.

The defining combinatorial properties of a triangulation (a "pseudomanifold with boundary"
whose boundary is the triangulated boundary of the simplex) are:

* every `m`-element face (*facet*) of a cell lies in exactly two cells if it is interior,
  and in exactly one cell if it lies in a proper face of the big simplex (equivalently,
  the union of the carriers of its vertices is not all of `I`);
* for every label `i`, the facets lying in the face opposite to `i` form, with the same
  carrier map, a triangulation of that `(m-1)`-dimensional face.

This is `Math.IsTriang` below.  A *Sperner colouring* is a map `c : V → ι` with
`c v ∈ car v` for every vertex `v`, and a cell is *rainbow* when the colours of its
vertices are exactly the labels `I`.
-/

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- All `k`-element subsets of cells of `cells` (the *facets* when `k` is one less than the
cardinality of the cells). -/
def facets (k : ℕ) (cells : Finset (Finset V)) : Finset (Finset V) :=
  cells.biUnion (fun s => Finset.powersetCard k s)

/-- The facets of `cells` lying in the face of the big simplex spanned by the labels `J`. -/
def faceCells (k : ℕ) (car : V → Finset ι) (J : Finset ι) (cells : Finset (Finset V)) :
    Finset (Finset V) :=
  {f ∈ facets k cells | f.biUnion car ⊆ J}

/-- `IsTriang m I car cells` says that `cells` is a triangulation of the `m`-dimensional
simplex whose vertices are labelled by `I`, with carrier map `car`. -/
def IsTriang : ℕ → Finset ι → (V → Finset ι) → Finset (Finset V) → Prop
  | 0, I, car, cells =>
      I.card = 1 ∧ cells.card = 1 ∧ (∀ s ∈ cells, s.card = 1) ∧
        (∀ s ∈ cells, ∀ v ∈ s, car v ⊆ I)
  | (m + 1), I, car, cells =>
      I.card = m + 2 ∧
      (∀ s ∈ cells, s.card = m + 2) ∧
      (∀ s ∈ cells, ∀ v ∈ s, car v ⊆ I) ∧
      (∀ f ∈ facets (m + 1) cells,
        #{s ∈ cells | f ⊆ s} = if f.biUnion car = I then 2 else 1) ∧
      (∀ i ∈ I, IsTriang m (I.erase i) car (faceCells (m + 1) car (I.erase i) cells))

/-- The rainbow cells of a colouring: those whose vertex colours are exactly the labels `I`. -/
def rainbowCells (I : Finset ι) (c : V → ι) (cells : Finset (Finset V)) : Finset (Finset V) :=
  {s ∈ cells | s.image c = I}

/-! ## Auxiliary combinatorial lemmas -/

/-- The `n`-element subsets of an `(n+1)`-element set are exactly the sets obtained by
deleting one element. -/
lemma powersetCard_pred (s : Finset V) (n : ℕ) (hs : s.card = n + 1) :
    Finset.powersetCard n s = s.image (fun w => s.erase w) := by
  ext f
  simp only [Finset.mem_powersetCard, Finset.mem_image]
  constructor
  · rintro ⟨hfs, hfc⟩
    have hss : f ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hfs, by intro h; rw [h, hs] at hfc; omega⟩
    obtain ⟨w, hw, hwf⟩ := Finset.exists_of_ssubset hss
    refine ⟨w, hw, ?_⟩
    have h1 : f ⊆ s.erase w := fun x hx => Finset.mem_erase.mpr ⟨fun h => hwf (h ▸ hx), hfs hx⟩
    have h2 : (s.erase w).card = n := by rw [Finset.card_erase_of_mem hw, hs]; omega
    exact (Finset.eq_of_subset_of_card_le h1 (by omega)).symm
  · rintro ⟨w, hw, rfl⟩
    exact ⟨Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hw, hs]; omega⟩

/-- The image of a set with one vertex deleted, for a colouring injective on the set. -/
lemma image_erase_injOn {s : Finset V} {c : V → ι} (h : Set.InjOn c s) {w : V} (hw : w ∈ s) :
    (s.erase w).image c = (s.image c).erase (c w) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
    exact ⟨fun hcon => hne (h ha hw hcon), a, ha, rfl⟩
  · rintro ⟨hx, a, ha, rfl⟩
    exact ⟨a, ⟨fun hcon => hx (by rw [hcon]), ha⟩, rfl⟩

/-- Counting facets of a cell with a given colour set can be done by counting the deleted
vertex instead. -/
lemma card_doors_eq (s : Finset V) (c : V → ι) (J : Finset ι) (n : ℕ) (hs : s.card = n + 2) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J}
      = #{w ∈ s | (s.erase w).image c = J} := by
  rw [powersetCard_pred s (n + 1) hs, Finset.filter_image, Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
  exact (Finset.erase_inj s ha.1).mp hab

/-- A rainbow cell has exactly one facet missing the colour `i`. -/
lemma card_doors_rainbow {s : Finset V} {c : V → ι} {I J : Finset ι} {i : ι} {n : ℕ}
    (hs : s.card = n + 2) (hI : I.card = n + 2) (hi : i ∈ I) (hJ : J = I.erase i)
    (himg : s.image c = I) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J} = 1 := by
  rw [card_doors_eq s c J n hs]
  have hinj : Set.InjOn c s := Finset.injOn_of_card_image_eq (by rw [himg, hI, hs])
  have key : ∀ w ∈ s, ((s.erase w).image c = J ↔ c w = i) := by
    intro w hw
    rw [image_erase_injOn hinj hw, himg, hJ]
    exact Finset.erase_inj I (himg ▸ Finset.mem_image_of_mem c hw)
  have hset : {w ∈ s | (s.erase w).image c = J} = {w ∈ s | c w = i} :=
    Finset.filter_congr (fun w hw => by simp [key w hw])
  rw [hset, Finset.card_eq_one]
  have hmem : i ∈ s.image c := by rw [himg]; exact hi
  obtain ⟨v, hv, hcv⟩ := Finset.mem_image.mp hmem
  refine ⟨v, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨by simp [hv, hcv], ?_⟩
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact hinj hx.1 hv (by rw [hx.2, hcv])

/-- If the colours of a cell are exactly `J` (so one colour is repeated), the cell has
exactly two facets with colour set `J`. -/
lemma card_doors_double {s : Finset V} {c : V → ι} {J : Finset ι} {n : ℕ}
    (hs : s.card = n + 2) (hJ : J.card = n + 1) (himg : s.image c = J) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J} = 2 := by
  rw [card_doors_eq s c J n hs]
  obtain ⟨u, hu, v, hv, huv, hcuv⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by omega : J.card < s.card)
      (fun x hx => by rw [← himg]; exact Finset.mem_image_of_mem c hx)
  have hkeep : ∀ a b : V, a ∈ s → b ∈ s → a ≠ b → c a = c b → (s.erase a).image c = J := by
    intro a b ha hb hab hcab
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      rw [← himg]
      exact Finset.mem_image_of_mem c (Finset.mem_of_mem_erase ht)
    · intro x hx
      rw [← himg] at hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      by_cases h : t = a
      · subst h
        exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨fun h => hab h.symm, hb⟩, hcab.symm⟩
      · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨h, ht⟩, rfl⟩
  have hother : ∀ w ∈ s, w ≠ u → w ≠ v → (s.erase w).image c ≠ J := by
    intro w hw hwu hwv
    have hu' : u ∈ (s.erase w).erase v :=
      Finset.mem_erase.mpr ⟨huv, Finset.mem_erase.mpr ⟨fun h => hwu h.symm, hu⟩⟩
    have hv' : v ∈ s.erase w := Finset.mem_erase.mpr ⟨fun h => hwv h.symm, hv⟩
    have heq : (s.erase w).image c = ((s.erase w).erase v).image c := by
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
        by_cases h : t = v
        · subst h
          exact Finset.mem_image.mpr ⟨u, hu', hcuv⟩
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨h, ht⟩, rfl⟩
      · exact Finset.image_subset_image (Finset.erase_subset _ _)
    intro hcon
    have hcard : ((s.erase w).erase v).card = n := by
      rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hw, hs]; omega
    have hle := Finset.card_image_le (s := ((s.erase w).erase v)) (f := c)
    rw [← heq, hcon, hJ, hcard] at hle
    omega
  have hset : {w ∈ s | (s.erase w).image c = J} = {u, v} := by
    apply Finset.Subset.antisymm
    · intro w hw
      simp only [Finset.mem_filter] at hw
      by_contra hcon
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
      exact hother w hw.1 hcon.1 hcon.2 hw.2
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hu, hkeep w v hu hv huv hcuv⟩
      · exact Finset.mem_filter.mpr ⟨hv, hkeep w u hv hu (Ne.symm huv) hcuv.symm⟩
  rw [hset, Finset.card_pair huv]

omit [DecidableEq V] in
/-- A cell whose colour set is neither `I` nor `J = I.erase i` has no facet with colour
set `J`. -/
lemma card_doors_zero {s : Finset V} {c : V → ι} {I J : Finset ι} {i : ι} {n : ℕ}
    (hi : i ∈ I) (hJ : J = I.erase i) (hsub : s.image c ⊆ I)
    (h1 : s.image c ≠ I) (h2 : s.image c ≠ J) :
    #{f ∈ Finset.powersetCard (n + 1) s | f.image c = J} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f hf
  rw [Finset.mem_powersetCard] at hf
  intro hcon
  have hJsub : J ⊆ s.image c := by
    rw [← hcon]; exact Finset.image_subset_image hf.1
  by_cases hii : i ∈ s.image c
  · exact h1 (Finset.Subset.antisymm hsub (by
      rw [← Finset.insert_erase hi, ← hJ, Finset.insert_subset_iff]
      exact ⟨hii, hJsub⟩))
  · refine h2 (Finset.Subset.antisymm ?_ hJsub)
    intro x hx
    rw [hJ, Finset.mem_erase]
    exact ⟨fun h => hii (h ▸ hx), hsub hx⟩

omit [DecidableEq V] in
/-- Double counting: the number of incident pairs computed in the two possible orders. -/
lemma sum_card_filter_comm (A B : Finset (Finset V)) (R : Finset V → Finset V → Prop)
    [DecidableRel R] :
    ∑ s ∈ A, #{f ∈ B | R s f} = ∑ f ∈ B, #{s ∈ A | R s f} := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-! ## Sperner's lemma -/

/-- **Sperner's lemma**: every Sperner colouring of a triangulated simplex has an odd
number of rainbow cells. -/
theorem sperner_lemma {m : ℕ} {I : Finset ι} {car : V → Finset ι} {cells : Finset (Finset V)}
    (h : IsTriang m I car cells) (c : V → ι) (hc : ∀ v, c v ∈ car v) :
    Odd #(rainbowCells I c cells) := by
  induction m generalizing I cells with
  | zero =>
    obtain ⟨hI1, hcard1, hs1, hcarsub⟩ := h
    have hall : rainbowCells I c cells = cells := by
      rw [rainbowCells]
      refine Finset.filter_true_of_mem ?_
      intro s hs
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (hs1 s hs)
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI1
      have hmem : c v ∈ ({a} : Finset ι) := hcarsub _ hs v (by simp) (hc v)
      simp only [Finset.mem_singleton] at hmem
      simp [hmem]
    rw [hall, hcard1]
    exact odd_one
  | succ n ih =>
    obtain ⟨hIcard, hcellcard, hcarsub, hfacet, hrec⟩ := h
    obtain ⟨i, hi⟩ : ∃ i, i ∈ I := Finset.card_pos.mp (by omega)
    have hJcard : (I.erase i).card = n + 1 := by rw [Finset.card_erase_of_mem hi, hIcard]; omega
    have hIJ : I ≠ I.erase i := by
      intro hcon; rw [← hcon] at hJcard; omega
    -- the "doors": facets whose colour set is exactly `I.erase i`
    have himgsub : ∀ s ∈ cells, s.image c ⊆ I := by
      intro s hs x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact hcarsub s hs v hv (hc v)
    have hLHS : ∀ s ∈ cells,
        #{f ∈ {g ∈ facets (n + 1) cells | g.image c = I.erase i} | f ⊆ s}
          = (if s.image c = I then 1 else 0) + 2 * (if s.image c = I.erase i then 1 else 0) := by
      intro s hs
      have hset : {f ∈ {g ∈ facets (n + 1) cells | g.image c = I.erase i} | f ⊆ s}
          = {f ∈ Finset.powersetCard (n + 1) s | f.image c = I.erase i} := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_powersetCard, facets, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨⟨t, ht, hft⟩, himg⟩, hfs⟩
          exact ⟨⟨hfs, hft.2⟩, himg⟩
        · rintro ⟨⟨hfs, hfc⟩, himg⟩
          exact ⟨⟨⟨s, hs, ⟨hfs, hfc⟩⟩, himg⟩, hfs⟩
      rw [hset]
      by_cases h1 : s.image c = I
      · rw [card_doors_rainbow (hcellcard s hs) hIcard hi rfl h1]
        simp [h1, hIJ]
      · by_cases h2 : s.image c = I.erase i
        · rw [card_doors_double (hcellcard s hs) hJcard h2]
          simp [h2, hi]
        · rw [card_doors_zero hi rfl (himgsub s hs) h1 h2]
          simp [h1, h2]
    have hRHS : ∀ f ∈ {g ∈ facets (n + 1) cells | g.image c = I.erase i},
        #{s ∈ cells | f ⊆ s}
          = 2 * (if f.biUnion car = I then 1 else 0)
            + (if f.biUnion car = I.erase i then 1 else 0) := by
      intro f hf
      simp only [Finset.mem_filter] at hf
      obtain ⟨hfacets, hfimg⟩ := hf
      have hsub : f.biUnion car ⊆ I := by
        obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hfacets
        rw [Finset.mem_powersetCard] at hft
        intro x hx
        obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
        exact hcarsub t ht v (hft.1 hv) hxv
      have hsupJ : I.erase i ⊆ f.biUnion car := by
        intro x hx
        rw [← hfimg] at hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_biUnion.mpr ⟨v, hv, hc v⟩
      have hdich : f.biUnion car = I ∨ f.biUnion car = I.erase i := by
        by_cases hii : i ∈ f.biUnion car
        · left
          refine Finset.Subset.antisymm hsub ?_
          rw [← Finset.insert_erase hi, Finset.insert_subset_iff]
          exact ⟨hii, hsupJ⟩
        · right
          refine Finset.Subset.antisymm ?_ hsupJ
          intro x hx
          exact Finset.mem_erase.mpr ⟨fun hcon => hii (hcon ▸ hx), hsub hx⟩
      rw [hfacet f hfacets]
      rcases hdich with hd | hd <;> simp [hd, hIJ, Ne.symm hIJ]
    have key := sum_card_filter_comm cells {g ∈ facets (n + 1) cells | g.image c = I.erase i}
      (fun s f => f ⊆ s)
    rw [Finset.sum_congr rfl hLHS, Finset.sum_congr rfl hRHS] at key
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter] at key
    -- the boundary doors are the rainbow cells of the induced triangulation of the face
    have hface : {f ∈ {g ∈ facets (n + 1) cells | g.image c = I.erase i} |
          f.biUnion car = I.erase i}
        = rainbowCells (I.erase i) c (faceCells (n + 1) car (I.erase i) cells) := by
      ext f
      simp only [rainbowCells, faceCells, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hfacets, himg⟩, hbi⟩
        exact ⟨⟨hfacets, hbi.le⟩, himg⟩
      · rintro ⟨⟨hfacets, hbi⟩, himg⟩
        refine ⟨⟨hfacets, himg⟩, Finset.Subset.antisymm hbi ?_⟩
        intro x hx
        rw [← himg] at hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_biUnion.mpr ⟨v, hv, hc v⟩
    have hodd : Odd #(rainbowCells (I.erase i) c (faceCells (n + 1) car (I.erase i) cells)) :=
      ih (hrec i hi)
    rw [← hface] at hodd
    obtain ⟨b, hb⟩ := hodd
    rw [Nat.odd_iff, rainbowCells]
    omega

/-! ## The hypotheses are satisfiable

The coarsest triangulation of the `m`-simplex, consisting of the single cell given by the
vertices of the simplex itself, satisfies `IsTriang`; this shows the hypothesis of
`sperner_lemma` is not vacuous.  See also `Math.isTriang_interval` below for a genuinely
subdivided (one-dimensional) example. -/
lemma isTriang_single (m : ℕ) (I : Finset ι) (hI : I.card = m + 1) :
    IsTriang m I (fun v => ({v} : Finset ι)) {I} := by
  induction m generalizing I with
  | zero =>
    refine ⟨hI, Finset.card_singleton _, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      rw [hs, hI]
    · intro s hs v hv x hx
      rw [Finset.mem_singleton] at hs hx
      rw [hs] at hv
      rwa [hx]
  | succ n ih =>
    have hfacet : ∀ f ∈ facets (n + 1) ({I} : Finset (Finset ι)), f ⊆ I ∧ f.card = n + 1 := by
      intro f hf
      obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hf
      rw [Finset.mem_singleton] at ht
      rw [Finset.mem_powersetCard, ht] at hft
      exact hft
    refine ⟨hI, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      rw [hs, hI]
    · intro s hs v hv x hx
      rw [Finset.mem_singleton] at hs hx
      rw [hs] at hv
      rwa [hx]
    · intro f hf
      obtain ⟨hfsub, hfcard⟩ := hfacet f hf
      have hne : f.biUnion (fun v => ({v} : Finset ι)) ≠ I := by
        rw [Finset.biUnion_singleton_eq_self]
        intro hcon
        rw [hcon, hI] at hfcard
        omega
      rw [if_neg hne]
      have : ({I} : Finset (Finset ι)).filter (fun s => f ⊆ s) = {I} :=
        Finset.filter_true_of_mem (by intro s hs; rw [Finset.mem_singleton] at hs; rwa [hs])
      rw [this, Finset.card_singleton]
    · intro i hi
      have hcard : (I.erase i).card = n + 1 := by
        rw [Finset.card_erase_of_mem hi, hI]; omega
      have hfc : faceCells (n + 1) (fun v => ({v} : Finset ι)) (I.erase i) {I}
          = {I.erase i} := by
        ext f
        simp only [faceCells, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hf, hbi⟩
          rw [Finset.biUnion_singleton_eq_self] at hbi
          exact Finset.eq_of_subset_of_card_le hbi (by rw [hcard, (hfacet f hf).2])
        · rintro rfl
          refine ⟨?_, by rw [Finset.biUnion_singleton_eq_self]⟩
          exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_singleton_self I,
            Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, hcard⟩⟩
      rw [hfc]
      exact ih (I.erase i) hcard

/-- Sperner's lemma applied to the coarsest triangulation: the identity colouring of the
single cell is a Sperner colouring with exactly one rainbow cell. -/
example (m : ℕ) (I : Finset ι) (hI : I.card = m + 1) :
    Odd #(rainbowCells I (id : ι → ι) {I}) :=
  sperner_lemma (isTriang_single m I hI) id (fun v => Finset.mem_singleton_self v)


/-! ### A genuinely subdivided example

The interval `[0, k]` subdivided into the `k` cells `{j, j+1}`, `j < k`, with the two
endpoints `0` and `k` carrying the two vertices of the `1`-simplex.  This shows that
`IsTriang` is satisfied by honest subdivisions, not only by the coarsest one. -/

/-- The cells of the subdivided interval. -/
def intervalCells (k : ℕ) : Finset (Finset ℕ) := (Finset.range k).image (fun j => {j, j + 1})

/-- The carrier map of the subdivided interval. -/
def intervalCar (k : ℕ) : ℕ → Finset ℕ :=
  fun v => if v = 0 then {0} else if v = k then {1} else {0, 1}

lemma intervalCar_zero (k : ℕ) : intervalCar k 0 = {0} := by simp [intervalCar]

lemma intervalCar_top {k : ℕ} (hk : 0 < k) : intervalCar k k = {1} := by
  rw [intervalCar]
  rw [if_neg (by omega), if_pos rfl]

lemma intervalCar_mid {k v : ℕ} (h0 : v ≠ 0) (hkk : v ≠ k) : intervalCar k v = {0, 1} := by
  rw [intervalCar]
  rw [if_neg h0, if_neg hkk]

lemma powersetCard_one_eq (s : Finset ℕ) :
    Finset.powersetCard 1 s = s.image (fun v => ({v} : Finset ℕ)) := by
  ext f
  simp only [Finset.mem_powersetCard, Finset.card_eq_one, Finset.mem_image]
  constructor
  · rintro ⟨hsub, v, rfl⟩
    exact ⟨v, hsub (by simp), rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨by simpa using hv, v, rfl⟩

lemma pair_inj {j j' : ℕ} (h : ({j, j + 1} : Finset ℕ) = {j', j' + 1}) : j = j' := by
  have h1 : j ∈ ({j', j' + 1} : Finset ℕ) := by rw [← h]; simp
  have h2 : j' ∈ ({j, j + 1} : Finset ℕ) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  omega

lemma mem_facets_interval {k : ℕ} (hk : 0 < k) {f : Finset ℕ} :
    f ∈ facets 1 (intervalCells k) ↔ ∃ v ≤ k, f = {v} := by
  simp only [facets, intervalCells, Finset.mem_biUnion, Finset.mem_image, powersetCard_one_eq,
    Finset.mem_range]
  constructor
  · rintro ⟨s, ⟨j, hj, rfl⟩, v, hv, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    exact ⟨v, by omega, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    by_cases h : v < k
    · exact ⟨{v, v + 1}, ⟨v, h, rfl⟩, v, by simp, rfl⟩
    · refine ⟨{k - 1, k - 1 + 1}, ⟨k - 1, by omega, rfl⟩, v, ?_, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega

lemma card_cells_containing {k v : ℕ} (hk : 0 < k) (hv : v ≤ k) :
    #{s ∈ intervalCells k | ({v} : Finset ℕ) ⊆ s} = if v = 0 ∨ v = k then 1 else 2 := by
  have hfil : {s ∈ intervalCells k | ({v} : Finset ℕ) ⊆ s}
      = ((Finset.range k).filter (fun j => v = j ∨ v = j + 1)).image
          (fun j => ({j, j + 1} : Finset ℕ)) := by
    rw [intervalCells, Finset.filter_image]
    congr 1
    refine Finset.filter_congr (fun j _ => ?_)
    simp only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [hfil, Finset.card_image_of_injOn (fun a _ b _ hab => pair_inj hab)]
  by_cases h0 : v = 0
  · have hset : (Finset.range k).filter (fun j => v = j ∨ v = j + 1) = {0} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hset, Finset.card_singleton, if_pos (Or.inl h0)]
  · by_cases hkk : v = k
    · have hset : (Finset.range k).filter (fun j => v = j ∨ v = j + 1) = {k - 1} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
      rw [hset, Finset.card_singleton, if_pos (Or.inr hkk)]
    · have hset : (Finset.range k).filter (fun j => v = j ∨ v = j + 1) = {v - 1, v} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [hset, Finset.card_pair (by omega), if_neg (by tauto)]

/-- The subdivided interval is a triangulation of the `1`-simplex; in particular the
hypotheses of `sperner_lemma` are satisfied by genuinely subdivided triangulations. -/
lemma isTriang_interval (k : ℕ) (hk : 0 < k) :
    IsTriang 1 ({0, 1} : Finset ℕ) (intervalCar k) (intervalCells k) := by
  have hcells : ∀ s ∈ intervalCells k, ∃ j < k, s = {j, j + 1} := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨j, Finset.mem_range.mp hj, rfl⟩
  have hcarsub : ∀ v : ℕ, intervalCar k v ⊆ ({0, 1} : Finset ℕ) := by
    intro v
    by_cases h0 : v = 0
    · rw [h0, intervalCar_zero]; decide
    · by_cases hkk : v = k
      · rw [hkk, intervalCar_top hk]; decide
      · rw [intervalCar_mid h0 hkk]
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := hcells s hs
    rw [Finset.card_pair (by omega)]
  · intro s _ v _
    exact hcarsub v
  · intro f hf
    obtain ⟨v, hv, rfl⟩ := (mem_facets_interval hk).mp hf
    rw [card_cells_containing hk hv, Finset.singleton_biUnion]
    by_cases h0 : v = 0
    · rw [if_pos (Or.inl h0), h0, intervalCar_zero, if_neg (by decide)]
    · by_cases hkk : v = k
      · rw [if_pos (Or.inr hkk), hkk, intervalCar_top hk, if_neg (by decide)]
      · rw [if_neg (by tauto), intervalCar_mid h0 hkk, if_pos rfl]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · have hJ : ({0, 1} : Finset ℕ).erase 0 = {1} := by decide
      rw [hJ]
      have hfc : faceCells 1 (intervalCar k) {1} (intervalCells k) = {{k}} := by
        ext f
        simp only [faceCells, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hf, hbi⟩
          obtain ⟨v, hv, rfl⟩ := (mem_facets_interval hk).mp hf
          rw [Finset.singleton_biUnion] at hbi
          by_cases h0 : v = 0
          · rw [h0, intervalCar_zero] at hbi
            exact absurd (hbi (by decide : (0 : ℕ) ∈ ({0} : Finset ℕ))) (by decide)
          · by_cases hkk : v = k
            · rw [hkk]
            · rw [intervalCar_mid h0 hkk] at hbi
              exact absurd (hbi (by decide : (0 : ℕ) ∈ ({0, 1} : Finset ℕ))) (by decide)
        · rintro rfl
          refine ⟨(mem_facets_interval hk).mpr ⟨k, le_refl k, rfl⟩, ?_⟩
          rw [Finset.singleton_biUnion, intervalCar_top hk]
      rw [hfc]
      refine ⟨by decide, Finset.card_singleton _, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.card_singleton]
      · intro s hs v hv
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.mem_singleton] at hv
        rw [hv, intervalCar_top hk]
    · have hJ : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
      rw [hJ]
      have hfc : faceCells 1 (intervalCar k) {0} (intervalCells k) = {{0}} := by
        ext f
        simp only [faceCells, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hf, hbi⟩
          obtain ⟨v, hv, rfl⟩ := (mem_facets_interval hk).mp hf
          rw [Finset.singleton_biUnion] at hbi
          by_cases h0 : v = 0
          · rw [h0]
          · by_cases hkk : v = k
            · rw [hkk, intervalCar_top hk] at hbi
              exact absurd (hbi (by decide : (1 : ℕ) ∈ ({1} : Finset ℕ))) (by decide)
            · rw [intervalCar_mid h0 hkk] at hbi
              exact absurd (hbi (by decide : (1 : ℕ) ∈ ({0, 1} : Finset ℕ))) (by decide)
        · rintro rfl
          refine ⟨(mem_facets_interval hk).mpr ⟨0, by omega, rfl⟩, ?_⟩
          rw [Finset.singleton_biUnion, intervalCar_zero]
      rw [hfc]
      refine ⟨by decide, Finset.card_singleton _, ?_, ?_⟩
      · intro s hs
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.card_singleton]
      · intro s hs v hv
        rw [Finset.mem_singleton] at hs
        rw [hs, Finset.mem_singleton] at hv
        rw [hv, intervalCar_zero]

/-- Sperner's lemma in dimension one: for any colouring of the vertices `0, …, k` of the
subdivided interval with `c 0 = 0` and `c k = 1` (equivalently, `c v ∈ intervalCar k v`),
an odd number of the subintervals `{j, j+1}` are rainbow. -/
theorem sperner_interval (k : ℕ) (hk : 0 < k) (c : ℕ → ℕ)
    (hc : ∀ v, c v ∈ intervalCar k v) :
    Odd #(rainbowCells ({0, 1} : Finset ℕ) c (intervalCells k)) :=
  sperner_lemma (isTriang_interval k hk) c hc

end Math

