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

namespace Math

open Finset

/-! ## Sperner's lemma

We formalise the classical combinatorial content of Sperner's lemma.

A *triangulated simplex* is described combinatorially: the vertices of the simplex are
labelled by a type `ι` (for the `n`-simplex, `ι = Fin (n+1)`), and a triangulation consists
of a finite abstract simplicial complex `faces` of *vertices* (of type `V`) together with,
for each vertex `v`, the *carrier* `carrier v ⊆ ι`: the (unique) minimal face of the big
simplex containing `v`.

For a face `t` of the triangulation, its *span* `span t = ⋃ {carrier v | v ∈ t}` is the
smallest face of the big simplex containing `t`.  For `F ⊆ ι`, the cells of the sub-simplex
spanned by `F` are the faces `s` with `span s ⊆ F` and `s.card = F.card`; these are exactly
the top-dimensional simplices of the induced triangulation of that face of the big simplex.

The single geometric input is then the *door axiom*: if `t` is a face lying inside the
sub-simplex `F` and of codimension one there, then `t` is contained in exactly two cells of
`F` when `t` is interior to `F` (i.e. `span t = F`), and in exactly one cell of `F` when `t`
lies in the boundary of `F` (i.e. `span t ⊊ F`).  This is the standard combinatorial
abstraction of "triangulation of a simplex"; see `Math.trivialTriangulation` and
`Math.subdividedSegment` below for instances.

A *Sperner colouring* assigns to each vertex `v` a colour `c v ∈ carrier v`; a cell of `F`
is *rainbow* if it carries all the colours of `F`.  Sperner's lemma says the number of
rainbow cells is odd. -/

/-- A combinatorial triangulation of the simplex with vertex set `ι`, whose vertices are of
type `V`. -/
structure TriangulatedSimplex (ι V : Type*) [DecidableEq ι] [DecidableEq V] where
  /-- The faces of the triangulation. -/
  faces : Finset (Finset V)
  /-- The carrier of a vertex: the minimal face of the big simplex containing it. -/
  carrier : V → Finset ι
  /-- The empty face belongs to the complex. -/
  empty_mem : (∅ : Finset V) ∈ faces
  /-- The set of faces is closed under passing to subsets. -/
  down_closed : ∀ ⦃s : Finset V⦄, s ∈ faces → ∀ ⦃t : Finset V⦄, t ⊆ s → t ∈ faces
  /-- The door axiom: a codimension-one face `t` of the sub-simplex spanned by `F` lies in
  exactly two cells of `F` if it is interior to `F`, and in exactly one cell of `F` if it
  lies on the boundary of `F`. -/
  door : ∀ (F : Finset ι) (t : Finset V), t ∈ faces → t.card + 1 = F.card →
      t.biUnion carrier ⊆ F →
      {s ∈ faces | s.card = F.card ∧ s.biUnion carrier ⊆ F ∧ t ⊆ s}.card
        = if t.biUnion carrier = F then 2 else 1

namespace TriangulatedSimplex

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] (T : TriangulatedSimplex ι V)

/-- The span of a face: the smallest face of the big simplex containing it. -/
def span (t : Finset V) : Finset ι := t.biUnion T.carrier

/-- The cells of the sub-simplex of the big simplex spanned by `F`. -/
def cells (F : Finset ι) : Finset (Finset V) :=
  {s ∈ T.faces | s.card = F.card ∧ T.span s ⊆ F}

/-- A colouring `c` is a Sperner colouring if each vertex gets a colour from its carrier. -/
def IsSpernerColoring (c : V → ι) : Prop := ∀ v : V, c v ∈ T.carrier v

/-- The rainbow cells of the sub-simplex spanned by `F`: cells carrying every colour of `F`. -/
def rainbowCells (c : V → ι) (F : Finset ι) : Finset (Finset V) :=
  {s ∈ T.cells F | s.image c = F}

end TriangulatedSimplex

/-! ### Auxiliary combinatorial lemmas -/

section Aux

variable {α β : Type*}

/-- Double counting of a relation between two finite sets. -/
lemma sum_card_filter_comm {A : Finset α} {B : Finset β} (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a ∈ A, {b ∈ B | r a b}.card = ∑ b ∈ B, {a ∈ A | r a b}.card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

lemma image_erase_of_injOn {s : Finset V} {c : V → ι}
    (hinj : ∀ u ∈ s, ∀ v ∈ s, c u = c v → u = v) {v : V} (hv : v ∈ s) :
    (s.erase v).image c = (s.image c).erase (c v) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxv, hxs⟩, rfl⟩
    exact ⟨fun h => hxv (hinj x hxs v hv h), x, hxs, rfl⟩
  · rintro ⟨hne, x, hxs, rfl⟩
    exact ⟨x, ⟨fun h => hne (by rw [h]), hxs⟩, rfl⟩


/-- Counting the codimension-one subfaces of `s` with a given property, by counting the
vertex that is removed. -/
lemma card_doorset {s : Finset V} {D : Finset (Finset V)} {k : ℕ} (hs : s.card = k + 1)
    (Q : Finset V → Prop) [DecidablePred Q]
    (hD : ∀ t : Finset V, t ⊆ s → (t ∈ D ↔ (t.card = k ∧ Q t))) :
    {t ∈ D | t ⊆ s}.card = {v ∈ s | Q (s.erase v)}.card := by
  have hcarderase : ∀ v ∈ s, (s.erase v).card = k := by
    intro v hv; rw [Finset.card_erase_of_mem hv, hs]; omega
  refine (Finset.card_bij (fun v _ => s.erase v) ?_ ?_ ?_).symm
  · intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    have hsub : s.erase v ⊆ s := Finset.erase_subset _ _
    exact ⟨(hD _ hsub).mpr ⟨hcarderase v hv.1, hv.2⟩, hsub⟩
  · intro v hv w hw h
    simp only [Finset.mem_filter] at hv hw
    have h' : s.erase v = s.erase w := h
    by_contra hne
    have hmem : v ∈ s.erase v := by rw [h']; exact Finset.mem_erase.mpr ⟨hne, hv.1⟩
    exact (Finset.mem_erase.mp hmem).1 rfl
  · intro t ht
    simp only [Finset.mem_filter] at ht
    obtain ⟨htD, hts⟩ := ht
    obtain ⟨hcard, hQ⟩ := (hD t hts).mp htD
    have hne : t ≠ s := by
      intro h; rw [h, hs] at hcard; omega
    obtain ⟨v, hvs, hvt⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hts, hne⟩)
    have hev : t = s.erase v :=
      Finset.eq_of_subset_of_card_le
        (fun x hx => Finset.mem_erase.mpr ⟨fun h => hvt (h ▸ hx), hts hx⟩)
        (by rw [hcarderase v hvs, hcard])
    refine ⟨v, ?_, hev.symm⟩
    simp only [Finset.mem_filter]
    exact ⟨hvs, hev ▸ hQ⟩

/-- If the cell `s` is rainbow, it has exactly one door. -/
lemma card_doorvertices_rainbow {s : Finset V} {c : V → ι} {F : Finset ι} {i₀ : ι}
    (hi₀ : i₀ ∈ F) (hcard : s.card = F.card) (himg : s.image c = F) :
    {v ∈ s | (s.erase v).image c = F.erase i₀}.card = 1 := by
  have hcimg : (s.image c).card = s.card := by rw [himg, hcard]
  have hinj : ∀ u ∈ s, ∀ v ∈ s, c u = c v → u = v := by
    intro u hu v hv huv
    exact Finset.injOn_of_card_image_eq hcimg (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
  have hset : {v ∈ s | (s.erase v).image c = F.erase i₀} = {v ∈ s | c v = i₀} := by
    apply Finset.filter_congr
    intro v hv
    rw [image_erase_of_injOn hinj hv, himg]
    constructor
    · intro h
      by_contra hne
      have h1 : i₀ ∈ F.erase (c v) := Finset.mem_erase.mpr ⟨fun h' => hne h'.symm, hi₀⟩
      rw [h] at h1
      exact (Finset.mem_erase.mp h1).1 rfl
    · intro h; rw [h]
  rw [hset]
  obtain ⟨v, hvs, hv⟩ : ∃ v ∈ s, c v = i₀ := by
    have : i₀ ∈ s.image c := by rw [himg]; exact hi₀
    simpa using this
  rw [Finset.card_eq_one]
  refine ⟨v, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hws, hw⟩
    exact hinj w hws v hvs (by rw [hw, hv])
  · rintro rfl; exact ⟨hvs, hv⟩

/-- If the cell `s` is not rainbow, it has an even number of doors. -/
lemma card_doorvertices_not_rainbow {s : Finset V} {c : V → ι} {F : Finset ι} {i₀ : ι}
    (hi₀ : i₀ ∈ F) (hcard : s.card = F.card) (hsub : s.image c ⊆ F) (hnr : s.image c ≠ F) :
    {v ∈ s | (s.erase v).image c = F.erase i₀}.card % 2 = 0 := by
  by_cases hF' : F.erase i₀ ⊆ s.image c
  · -- then `s.image c = F.erase i₀`, and there are exactly two doors
    have himg : s.image c = F.erase i₀ := by
      refine Finset.Subset.antisymm ?_ hF'
      intro i hi
      rcases eq_or_ne i i₀ with rfl | hii
      · exact absurd (Finset.Subset.antisymm hsub (fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · exact hi
          · exact hF' (Finset.mem_erase.mpr ⟨hji, hj⟩))) hnr
      · exact Finset.mem_erase.mpr ⟨hii, hsub hi⟩
    have hcards : (s.image c).card < s.card := by
      rw [himg, hcard, Finset.card_erase_of_mem hi₀]
      have : 0 < F.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    obtain ⟨u, hu, w, hw, huw, hcuw⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcards
        (fun x hx => Finset.mem_image_of_mem c hx)
    -- erasing either `u` or `w` does not change the image
    have himg_erase : ∀ (a b : V), a ∈ s → b ∈ s → a ≠ b → c a = c b →
        (s.erase a).image c = s.image c := by
      intro a b ha hb hab hcab
      refine Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _)) ?_
      intro i hi
      obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hi
      rcases eq_or_ne x a with rfl | hxa
      · exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩, hcab.symm⟩
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxa, hxs⟩, rfl⟩
    have himgu : (s.erase u).image c = s.image c := himg_erase u w hu hw huw hcuw
    have himgw : (s.erase w).image c = s.image c := himg_erase w u hw hu huw.symm hcuw.symm
    have hcardeu : ((s.erase u).image c).card = (s.erase u).card := by
      rw [himgu, himg, Finset.card_erase_of_mem hu, hcard, Finset.card_erase_of_mem hi₀]
    have hinju : ∀ x ∈ s.erase u, ∀ y ∈ s.erase u, c x = c y → x = y := by
      intro x hx y hy hxy
      exact Finset.injOn_of_card_image_eq hcardeu (Finset.mem_coe.mpr hx)
        (Finset.mem_coe.mpr hy) hxy
    have hudoor : (s.erase u).image c = F.erase i₀ := by rw [himgu, himg]
    have hwdoor : (s.erase w).image c = F.erase i₀ := by rw [himgw, himg]
    have hset : {v ∈ s | (s.erase v).image c = F.erase i₀} = {u, w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hvs, hv⟩
        by_contra hcon
        push_neg at hcon
        obtain ⟨hvu, hvw⟩ := hcon
        have hcv : c v ∈ (s.erase v).image c := by
          rw [hv, ← himg]; exact Finset.mem_image_of_mem c hvs
        obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp hcv
        obtain ⟨hxv, hxs⟩ := Finset.mem_erase.mp hx
        rcases eq_or_ne x u with hxu | hxu
        · refine hvw (hinju v (Finset.mem_erase.mpr ⟨hvu, hvs⟩) w
            (Finset.mem_erase.mpr ⟨huw.symm, hw⟩) ?_)
          rw [← hcx, hxu, hcuw]
        · exact hxv (hinju x (Finset.mem_erase.mpr ⟨hxu, hxs⟩) v
            (Finset.mem_erase.mpr ⟨hvu, hvs⟩) hcx)
      · intro h
        rcases h with h | h
        · subst h; exact ⟨hu, hudoor⟩
        · subst h; exact ⟨hw, hwdoor⟩
    rw [hset, Finset.card_pair huw]
  · -- no doors at all
    have hempty : {v ∈ s | (s.erase v).image c = F.erase i₀} = ∅ := by
      apply Finset.filter_false_of_mem
      intro v _ h
      exact hF' (h ▸ Finset.image_subset_image (Finset.erase_subset _ _))
    rw [hempty]
    simp

end Aux

/-! ### Sperner's lemma -/

namespace TriangulatedSimplex

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] (T : TriangulatedSimplex ι V)

lemma span_mono {s t : Finset V} (h : s ⊆ t) : T.span s ⊆ T.span t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma image_subset_span {c : V → ι} (hc : T.IsSpernerColoring c) (s : Finset V) :
    s.image c ⊆ T.span s := by
  intro i hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_biUnion.mpr ⟨v, hv, hc v⟩

lemma mem_cells_iff {F : Finset ι} {s : Finset V} :
    s ∈ T.cells F ↔ s ∈ T.faces ∧ s.card = F.card ∧ T.span s ⊆ F := by
  simp [cells]

/-- The key induction: for every face `F` of the big simplex, the number of rainbow cells
of the induced triangulation of `F` is odd. -/
theorem odd_card_rainbowCells {c : V → ι} (hc : T.IsSpernerColoring c) (F : Finset ι) :
    Odd (T.rainbowCells c F).card := by
  induction F using Finset.strongInduction with
  | _ F ih =>
  rcases F.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · -- base case: the unique cell of the empty simplex is the empty face, which is rainbow
    have hrb : T.rainbowCells c ∅ = {∅} := by
      ext s
      simp only [rainbowCells, cells, Finset.mem_filter, Finset.mem_singleton,
        Finset.card_empty]
      constructor
      · rintro ⟨⟨-, hs, -⟩, -⟩
        exact Finset.card_eq_zero.mp hs
      · rintro rfl
        exact ⟨⟨T.empty_mem, rfl, by simp [span]⟩, by simp⟩
    rw [hrb]
    simp
  · -- induction step
    set F' : Finset ι := F.erase i₀ with hF'
    have hF'sub : F' ⊂ F := Finset.erase_ssubset hi₀
    have hF'card : F'.card + 1 = F.card := by
      rw [hF', Finset.card_erase_of_mem hi₀]
      have : 0 < F.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    -- the set of doors
    set D : Finset (Finset V) :=
      {t ∈ T.faces | t.card = F'.card ∧ T.span t ⊆ F ∧ t.image c = F'} with hD
    have hmemD : ∀ t : Finset V,
        t ∈ D ↔ (t ∈ T.faces ∧ t.card = F'.card ∧ T.span t ⊆ F ∧ t.image c = F') := by
      intro t; simp [hD]
    -- first count: over cells
    have hcount1 : ((∑ s ∈ T.cells F, {t ∈ D | t ⊆ s}.card : ℕ) : ZMod 2)
        = ((T.rainbowCells c F).card : ZMod 2) := by
      have hterm : ∀ s ∈ T.cells F,
          (({t ∈ D | t ⊆ s}.card : ℕ) : ZMod 2) = (if s.image c = F then 1 else 0) := by
        intro s hs
        rw [T.mem_cells_iff] at hs
        obtain ⟨hsf, hscard, hspan⟩ := hs
        have hsub : s.image c ⊆ F := (T.image_subset_span hc s).trans hspan
        have hkey : {t ∈ D | t ⊆ s}.card
            = {v ∈ s | (s.erase v).image c = F'}.card := by
          refine card_doorset (k := F'.card) (by omega) (fun t => t.image c = F') ?_
          intro t hts
          rw [hmemD]
          constructor
          · rintro ⟨-, h1, -, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨T.down_closed hsf hts, h1, (T.span_mono hts).trans hspan, h2⟩
        rw [hkey]
        by_cases hrb : s.image c = F
        · rw [if_pos hrb, card_doorvertices_rainbow hi₀ hscard hrb]
          norm_num
        · rw [if_neg hrb]
          exact ZMod.natCast_eq_zero_iff_even.mpr
            (Nat.even_iff.mpr (card_doorvertices_not_rainbow hi₀ hscard hsub hrb))
      rw [Nat.cast_sum, Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const,
        Finset.sum_const]
      simp only [mul_zero, add_zero, nsmul_eq_mul, mul_one]
      rfl
    -- second count: over doors
    have hcount2 : ((∑ t ∈ D, {s ∈ T.cells F | t ⊆ s}.card : ℕ) : ZMod 2)
        = ((T.rainbowCells c F').card : ZMod 2) := by
      have hterm : ∀ t ∈ D,
          (({s ∈ T.cells F | t ⊆ s}.card : ℕ) : ZMod 2) = (if T.span t = F' then 1 else 0) := by
        intro t ht
        rw [hmemD] at ht
        obtain ⟨htf, htcard, htspan, htimg⟩ := ht
        have hdoor : {s ∈ T.faces | s.card = F.card ∧ T.span s ⊆ F ∧ t ⊆ s}.card
            = if T.span t = F then 2 else 1 := T.door F t htf (by omega) htspan
        have hfilter : {s ∈ T.cells F | t ⊆ s}
            = {s ∈ T.faces | s.card = F.card ∧ T.span s ⊆ F ∧ t ⊆ s} := by
          simp [cells, Finset.filter_filter, and_assoc]
        rw [hfilter, hdoor]
        -- `F' ⊆ span t ⊆ F`, so `span t` is either `F'` or `F`
        have hF'sub' : F' ⊆ T.span t := by
          rw [← htimg]; exact T.image_subset_span hc t
        by_cases hst : T.span t = F
        · rw [if_pos hst, if_neg (by rw [hst]; exact fun h => hF'sub.ne h.symm)]
          decide
        · rw [if_neg hst]
          have hspF' : T.span t = F' := by
            refine Finset.Subset.antisymm ?_ hF'sub'
            intro i hi
            rcases eq_or_ne i i₀ with rfl | hii
            · refine absurd (Finset.Subset.antisymm htspan (fun j hj => ?_)) hst
              rcases eq_or_ne j i with rfl | hji
              · exact hi
              · exact hF'sub' (Finset.mem_erase.mpr ⟨hji, hj⟩)
            · exact Finset.mem_erase.mpr ⟨hii, htspan hi⟩
          rw [if_pos hspF']
          norm_num
      -- the doors with span `F'` are exactly the rainbow cells of `F'`
      have hsets : {t ∈ D | T.span t = F'} = T.rainbowCells c F' := by
        ext t
        simp only [Finset.mem_filter, hmemD, rainbowCells, cells, Finset.mem_filter]
        constructor
        · rintro ⟨⟨htf, htcard, -, htimg⟩, hspan⟩
          exact ⟨⟨htf, htcard, by rw [hspan]⟩, htimg⟩
        · rintro ⟨⟨htf, htcard, hspan⟩, htimg⟩
          have hF'sub' : F' ⊆ T.span t := by rw [← htimg]; exact T.image_subset_span hc t
          exact ⟨⟨htf, htcard, hspan.trans hF'sub.subset, htimg⟩,
            Finset.Subset.antisymm hspan hF'sub'⟩
      rw [Nat.cast_sum, Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const,
        Finset.sum_const]
      simp only [mul_zero, add_zero, nsmul_eq_mul, mul_one]
      rw [hsets]
    -- combine
    have hswap : ∑ s ∈ T.cells F, {t ∈ D | t ⊆ s}.card
        = ∑ t ∈ D, {s ∈ T.cells F | t ⊆ s}.card :=
      sum_card_filter_comm (fun s t => t ⊆ s)
    have hcong : ((T.rainbowCells c F).card : ZMod 2) = ((T.rainbowCells c F').card : ZMod 2) := by
      rw [← hcount1, ← hcount2, hswap]
    have hodd' := ih F' hF'sub
    rw [← ZMod.natCast_eq_one_iff_odd] at hodd' ⊢
    rw [hcong]
    exact hodd'

end TriangulatedSimplex

/-- **Sperner's lemma.**  For every Sperner colouring of a combinatorially triangulated
simplex, the number of rainbow cells is odd. -/
theorem sperner_lemma {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V]
    (T : TriangulatedSimplex ι V) (c : V → ι) (hc : T.IsSpernerColoring c) :
    Odd (T.rainbowCells c Finset.univ).card :=
  T.odd_card_rainbowCells hc Finset.univ

/-- **Existence version of Sperner's lemma**: there is at least one rainbow cell. -/
theorem exists_rainbowCell {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V]
    (T : TriangulatedSimplex ι V) (c : V → ι) (hc : T.IsSpernerColoring c) :
    ∃ s ∈ T.cells (Finset.univ : Finset ι), s.image c = Finset.univ := by
  have h := sperner_lemma T c hc
  have hne : (T.rainbowCells c (Finset.univ : Finset ι)).Nonempty := by
    rw [← Finset.card_pos]
    rcases h with ⟨m, hm⟩
    omega
  obtain ⟨s, hs⟩ := hne
  rw [TriangulatedSimplex.rainbowCells, Finset.mem_filter] at hs
  exact ⟨s, hs.1, hs.2⟩

/-! ### Examples

Instances of `Math.TriangulatedSimplex`, showing that the axioms are consistent and that
they are satisfied by genuine (subdivided) triangulations in dimensions 1 and 2. -/

/-- The trivial triangulation of the simplex on the vertex set `ι`: the simplex itself. -/
def trivialTriangulation (ι : Type*) [DecidableEq ι] [Fintype ι] : TriangulatedSimplex ι ι where
  faces := Finset.univ
  carrier v := {v}
  empty_mem := Finset.mem_univ _
  down_closed := by intro s _ t _; exact Finset.mem_univ _
  door := by
    intro F t _ hcard hspan
    simp only [Finset.biUnion_singleton_eq_self] at hspan ⊢
    have hset : {s ∈ (Finset.univ : Finset (Finset ι)) | s.card = F.card ∧ s ⊆ F ∧ t ⊆ s}
        = {F} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact Finset.eq_of_subset_of_card_le h2 (le_of_eq h1.symm)
      · rintro rfl
        exact ⟨rfl, Finset.Subset.refl _, hspan⟩
    rw [hset, Finset.card_singleton, if_neg]
    intro h
    rw [h] at hcard
    omega

/-- The segment `[0,1]` subdivided into the two segments `[0, ½]` and `[½, 1]`: the vertex
`0` sits at the endpoint of colour `0`, the vertex `1` is the interior midpoint and the
vertex `2` sits at the endpoint of colour `1`. -/
def subdividedSegment : TriangulatedSimplex (Fin 2) (Fin 3) where
  faces := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}}
  carrier v := if v = 0 then {0} else if v = 2 then {1} else {0, 1}
  empty_mem := by decide
  down_closed := by decide
  door := by decide

/-- The Sperner colouring of the subdivided segment sending the midpoint to colour `0`. -/
def segmentColoring : Fin 3 → Fin 2 := ![0, 0, 1]

example : subdividedSegment.IsSpernerColoring segmentColoring := by
  intro v
  fin_cases v <;> decide

/-- In this example there is exactly one rainbow cell, namely `{1, 2}`. -/
example : subdividedSegment.rainbowCells segmentColoring Finset.univ = {{1, 2}} := by decide

/-- The triangle subdivided into four triangles by its edge midpoints: the corners `0, 1, 2`
carry the three colours, and `3, 4, 5` are the midpoints of the edges `01`, `12`, `02`. -/
def midpointTriangle : TriangulatedSimplex (Fin 3) (Fin 6) where
  faces := ({0, 3, 5} : Finset (Fin 6)).powerset ∪ ({3, 1, 4} : Finset (Fin 6)).powerset ∪
      ({5, 4, 2} : Finset (Fin 6)).powerset ∪ ({3, 4, 5} : Finset (Fin 6)).powerset
  carrier v := if v = 0 then {0} else if v = 1 then {1} else if v = 2 then {2}
    else if v = 3 then {0, 1} else if v = 4 then {1, 2} else {0, 2}
  empty_mem := by decide
  down_closed := by decide
  door := by decide

/-- A Sperner colouring of the subdivided triangle. -/
def triangleColoring : Fin 6 → Fin 3 := ![0, 1, 2, 1, 2, 0]

example : midpointTriangle.IsSpernerColoring triangleColoring := by
  intro v
  fin_cases v <;> decide

/-- Here exactly one of the four small triangles is rainbow, namely `{3, 4, 5}`. -/
example : midpointTriangle.rainbowCells triangleColoring Finset.univ = {{3, 4, 5}} := by decide

end Math

