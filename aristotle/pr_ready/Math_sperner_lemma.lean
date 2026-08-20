/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Statement: Every Sperner coloring of a triangulated simplex has an odd number of rainbow cells.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

variable {V : Type*} [DecidableEq V]

/-- The `k`-dimensional faces (as `Finset`s of `k` vertices) occurring in the cells of `K`. -/
def facets (K : Finset (Finset V)) (k : ℕ) : Finset (Finset V) :=
  K.biUnion (fun s => s.powersetCard k)

/-- The subcomplex of `K` living on the face `B` of the simplex: those codimension-one
faces of cells of `K` all of whose vertices are carried by `B`. -/
def subComplex (K : Finset (Finset V)) (carr : V → Finset ℕ) (B : Finset ℕ) (k : ℕ) :
    Finset (Finset V) :=
  (facets K k).filter (fun f => f.biUnion carr ⊆ B)

/-- Combinatorial description of a triangulation of the simplex with vertex set `A`
(`A.card = n+1`, so `n` is the dimension).

* `K` is the finite set of top-dimensional cells, each an `(n+1)`-element set of vertices;
* `carr v` is the (nonempty) face of the simplex carrying the vertex `v`, so `carr v ⊆ A`;
* every codimension-one face `f` of a cell lies in exactly two cells if it is interior
  (equivalently, its vertices together span the whole simplex, `f.biUnion carr = A`) and in
  exactly one cell if it lies on the boundary;
* for each vertex `a` of the simplex, the faces carried by the opposite facet `A.erase a`
  form a triangulation of that facet. -/
def IsTriangulation : ℕ → Finset ℕ → Finset (Finset V) → (V → Finset ℕ) → Prop
  | 0, A, K, carr =>
      A.card = 1 ∧ K.Nonempty ∧ (∀ s ∈ K, s.card = 1) ∧ (∀ s ∈ K, ∀ v ∈ s, carr v ⊆ A) ∧
      (∀ f ∈ facets K 0,
        (K.filter (fun s => f ⊆ s)).card = if f.biUnion carr = A then 2 else 1)
  | (n + 1), A, K, carr =>
      A.card = n + 2 ∧ K.Nonempty ∧ (∀ s ∈ K, s.card = n + 2) ∧ (∀ s ∈ K, ∀ v ∈ s, carr v ⊆ A) ∧
      (∀ f ∈ facets K (n + 1),
        (K.filter (fun s => f ⊆ s)).card = if f.biUnion carr = A then 2 else 1) ∧
      (∀ a ∈ A, IsTriangulation n (A.erase a) (subComplex K carr (A.erase a) (n + 1)) carr)

/-- Codimension-one faces of a nonempty finite set are exactly its one-point deletions. -/
lemma powersetCard_pred (s : Finset V) (hs : s.Nonempty) :
    s.powersetCard (s.card - 1) = s.image (fun v => s.erase v) := by
  ext f
  simp only [Finset.mem_powersetCard, Finset.mem_image]
  constructor
  · rintro ⟨hfs, hcard⟩
    have hsd : (s \ f).card = 1 := by
      rw [Finset.card_sdiff_of_subset hfs, hcard]
      have : 1 ≤ s.card := Finset.card_pos.mpr hs
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hsd
    have hvmem : v ∈ s \ f := by rw [hv]; simp
    have hvs : v ∈ s := (Finset.mem_sdiff.mp hvmem).1
    have hvf : v ∉ f := (Finset.mem_sdiff.mp hvmem).2
    refine ⟨v, hvs, ?_⟩
    apply Finset.Subset.antisymm
    · intro u hu
      rcases Finset.mem_erase.mp hu with ⟨hne, hus⟩
      by_contra huf
      have : u ∈ s \ f := Finset.mem_sdiff.mpr ⟨hus, huf⟩
      rw [hv] at this
      exact hne (Finset.mem_singleton.mp this)
    · intro u hu
      exact Finset.mem_erase.mpr ⟨fun h => hvf (h ▸ hu), hfs hu⟩
  · rintro ⟨v, hvs, rfl⟩
    exact ⟨Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hvs]⟩

/-- If the fibre sizes of a partition of a set of size `B.card + 1` into `B.card` nonempty
parts are given by `m`, then exactly one part has two elements and all others one. -/
lemma exists_double_fibre (B : Finset ℕ) (m : ℕ → ℕ) (hpos : ∀ b ∈ B, 1 ≤ m b)
    (hsum : ∑ b ∈ B, m b = B.card + 1) :
    ∃ b0 ∈ B, m b0 = 2 ∧ ∀ b ∈ B, b ≠ b0 → m b = 1 := by
  have hex : ∃ b0 ∈ B, 2 ≤ m b0 := by
    by_contra h
    push_neg at h
    have heq : ∀ b ∈ B, m b = 1 := fun b hb => le_antisymm (by have := h b hb; omega) (hpos b hb)
    rw [Finset.sum_congr rfl heq] at hsum
    simp at hsum
  obtain ⟨b0, hb0, hb0two⟩ := hex
  have hsplit : m b0 + ∑ b ∈ B.erase b0, m b = B.card + 1 := by
    rw [← hsum, Finset.add_sum_erase _ _ hb0]
  have hge : (B.erase b0).card ≤ ∑ b ∈ B.erase b0, m b := by
    calc (B.erase b0).card = ∑ _b ∈ B.erase b0, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun b hb => hpos b (Finset.mem_of_mem_erase hb))
  have hBcard : (B.erase b0).card = B.card - 1 := Finset.card_erase_of_mem hb0
  have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨b0, hb0⟩
  have hm0 : m b0 = 2 := by omega
  refine ⟨b0, hb0, hm0, ?_⟩
  intro b hb hne
  have hb' : b ∈ B.erase b0 := Finset.mem_erase.mpr ⟨hne, hb⟩
  have hsplit2 : m b + ∑ x ∈ (B.erase b0).erase b, m x = ∑ x ∈ B.erase b0, m x :=
    Finset.add_sum_erase _ _ hb'
  have hge2 : ((B.erase b0).erase b).card ≤ ∑ x ∈ (B.erase b0).erase b, m x := by
    calc ((B.erase b0).erase b).card = ∑ _x ∈ (B.erase b0).erase b, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum
      (fun x hx => hpos x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
  have hb2 : 2 ≤ B.card := by
    have : 1 ≤ (B.erase b0).card := Finset.card_pos.mpr ⟨b, hb'⟩
    omega
  have h2 : ((B.erase b0).erase b).card = B.card - 2 := by
    rw [Finset.card_erase_of_mem hb', hBcard]; omega
  have hbpos := hpos b hb
  omega

/-- Counting, modulo 2, the codimension-one faces of a cell `s` whose colours are exactly
`B = A.erase a`: there is exactly one if `s` is rainbow, and an even number otherwise. -/
lemma facet_parity (c : V → ℕ) (s : Finset V) (A : Finset ℕ) (a : ℕ)
    (ha : a ∈ A) (hcard : s.card = A.card) (hs : s.Nonempty) (hsub : s.image c ⊆ A) :
    ((s.powersetCard (s.card - 1)).filter (fun f => f.image c = A.erase a)).card % 2
      = if s.image c = A then 1 else 0 := by
  have hinj : Set.InjOn (fun v => s.erase v) s := by
    intro u hu v hv h
    by_contra hne
    have hmem : u ∈ s.erase v := Finset.mem_erase.mpr ⟨hne, hu⟩
    simp only at h
    rw [← h] at hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  have hTeq : ((s.powersetCard (s.card - 1)).filter (fun f => f.image c = A.erase a)).card
      = (s.filter (fun v => (s.erase v).image c = A.erase a)).card := by
    rw [powersetCard_pred s hs, Finset.filter_image,
      Finset.card_image_of_injOn (hinj.mono (by
        intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
        exact hx.1))]
  rw [hTeq]
  by_cases hrain : s.image c = A
  · rw [if_pos hrain]
    have hinjc : Set.InjOn c s := by
      apply Finset.injOn_of_card_image_eq
      rw [hrain, hcard]
    have himg_erase : ∀ v ∈ s, (s.erase v).image c = A.erase (c v) := by
      intro v hv
      ext b
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨u, ⟨hne, hus⟩, rfl⟩
        exact ⟨fun hcc => hne (hinjc hus hv hcc), hsub (Finset.mem_image_of_mem c hus)⟩
      · rintro ⟨hne, hbA⟩
        rw [← hrain] at hbA
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hbA
        exact ⟨u, ⟨fun h => hne (by rw [h]), hu⟩, rfl⟩
    have hfil : s.filter (fun v => (s.erase v).image c = A.erase a)
        = s.filter (fun v => c v = a) := by
      apply Finset.filter_congr
      intro v hv
      rw [himg_erase v hv]
      constructor
      · intro h
        by_contra hne
        have hvA : c v ∈ A := hsub (Finset.mem_image_of_mem c hv)
        have hmem : c v ∈ A.erase a := Finset.mem_erase.mpr ⟨hne, hvA⟩
        rw [← h] at hmem
        exact (Finset.mem_erase.mp hmem).1 rfl
      · intro h; rw [h]
    have haim : a ∈ s.image c := by rw [hrain]; exact ha
    obtain ⟨v0, hv0s, hv0⟩ := Finset.mem_image.mp haim
    have hsingle : s.filter (fun v => c v = a) = {v0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hvs, hcv⟩
        exact hinjc hvs hv0s (by rw [hcv, hv0])
      · rintro rfl
        exact ⟨hv0s, hv0⟩
    rw [hfil, hsingle]
    simp
  · rw [if_neg hrain]
    by_cases hB : s.image c = A.erase a
    · have hAcard : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
      have hBcard : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem ha
      have hsB : s.card = (A.erase a).card + 1 := by omega
      have hsum : ∑ b ∈ A.erase a, (s.filter (fun u => c u = b)).card
          = (A.erase a).card + 1 := by
        rw [← hsB, Finset.card_eq_sum_card_image c s, hB]
      have hpos : ∀ b ∈ A.erase a, 1 ≤ (s.filter (fun u => c u = b)).card := by
        intro b hb
        rw [← hB] at hb
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.card_pos.mpr ⟨v, by simp [hv]⟩
      obtain ⟨b0, hb0, hb0two, hb0rest⟩ := exists_double_fibre _ _ hpos hsum
      have hfil : s.filter (fun v => (s.erase v).image c = A.erase a)
          = s.filter (fun v => c v = b0) := by
        apply Finset.filter_congr
        intro v hv
        constructor
        · intro h
          by_contra hne
          have hvB : c v ∈ A.erase a := by rw [← hB]; exact Finset.mem_image_of_mem c hv
          have h1 : (s.filter (fun u => c u = c v)).card = 1 := hb0rest _ hvB hne
          have hnotmem : c v ∉ (s.erase v).image c := by
            intro hmem
            obtain ⟨u, hu, hcu⟩ := Finset.mem_image.mp hmem
            rcases Finset.mem_erase.mp hu with ⟨hne2, hus⟩
            have hpair : ({u, v} : Finset V) ⊆ s.filter (fun w => c w = c v) := by
              intro w hw
              rcases Finset.mem_insert.mp hw with rfl | hw
              · exact Finset.mem_filter.mpr ⟨hus, hcu⟩
              · rw [Finset.mem_singleton.mp hw]
                exact Finset.mem_filter.mpr ⟨hv, rfl⟩
            have hle := Finset.card_le_card hpair
            rw [Finset.card_insert_of_notMem (by simpa using hne2), Finset.card_singleton] at hle
            omega
          rw [h] at hnotmem
          exact hnotmem hvB
        · intro h
          have hcard2 : 1 < (s.filter (fun u => c u = b0)).card := by rw [hb0two]; omega
          obtain ⟨u, hu, hune⟩ := Finset.exists_mem_ne hcard2 v
          rcases Finset.mem_filter.mp hu with ⟨hus, hcu⟩
          have himg : (s.erase v).image c = s.image c := by
            apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
            intro b hb
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
            by_cases hwv : w = v
            · subst hwv
              exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨hune, hus⟩, by rw [hcu, h]⟩
            · exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, hw⟩, rfl⟩
          rw [himg, hB]
      rw [hfil, hb0two]
    · have hempty : s.filter (fun v => (s.erase v).image c = A.erase a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v hv hcon
        have hsubB : A.erase a ⊆ s.image c := by
          rw [← hcon]; exact Finset.image_subset_image (Finset.erase_subset _ _)
        have hane : a ∈ s.image c := by
          by_contra hno
          exact hB (Finset.Subset.antisymm
            (fun x hx => Finset.mem_erase.mpr ⟨fun h => hno (h ▸ hx), hsub hx⟩) hsubB)
        refine absurd (Finset.Subset.antisymm hsub ?_) hrain
        intro x hx
        by_cases hxa : x = a
        · rw [hxa]; exact hane
        · exact hsubB (Finset.mem_erase.mpr ⟨hxa, hx⟩)
      rw [hempty]
      simp

/-- **Sperner's lemma.**  For every Sperner colouring `c` of a triangulation `K` of the
`n`-dimensional simplex with vertex set `A` (each vertex `v` receives a colour `c v` belonging
to its carrier face `carr v`), the number of rainbow cells — cells whose vertices carry all
`n+1` colours — is odd. -/
theorem sperner_lemma (n : ℕ) (A : Finset ℕ) (K : Finset (Finset V))
    (carr : V → Finset ℕ) (c : V → ℕ)
    (hT : IsTriangulation n A K carr)
    (hc : ∀ s ∈ K, ∀ v ∈ s, c v ∈ carr v) :
    Odd ((K.filter (fun s => s.image c = A)).card) := by
  induction n generalizing A K with
  | zero =>
    obtain ⟨hA1, hKne, hcards, hcarr, hfacet⟩ := hT
    have hAne : A ≠ ∅ := by
      intro h; rw [h] at hA1; simp at hA1
    obtain ⟨s0, hs0⟩ := hKne
    have hmem : (∅ : Finset V) ∈ facets K 0 :=
      Finset.mem_biUnion.mpr ⟨s0, hs0, by simp⟩
    have hK1 : K.card = 1 := by
      have h := hfacet ∅ hmem
      have hne : (∅ : Finset V).biUnion carr ≠ A := by
        simp only [Finset.biUnion_empty]
        exact fun h => hAne h.symm
      rw [if_neg hne] at h
      simpa using h
    have hall : K.filter (fun s => s.image c = A) = K := by
      apply Finset.filter_true_of_mem
      intro s hs
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (hcards s hs)
      have hcv : c v ∈ A := hcarr _ hs v (by simp) (hc _ hs v (by simp))
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hA1
      simp only [Finset.mem_singleton] at hcv
      rw [Finset.image_singleton, hcv]
    rw [hall, hK1]
    exact odd_one
  | succ n ih =>
    obtain ⟨hAcard, hKne, hcards, hcarr, hfacet, hrec⟩ := hT
    obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    set B := A.erase a with hBdef
    set Fc := facets K (n + 1) with hFc
    set G := Fc.filter (fun f => f.image c = B) with hG
    have hcolA : ∀ s ∈ K, s.image c ⊆ A := by
      intro s hs b hb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact hcarr s hs v hv (hc s hs v hv)
    have hfacet_mem : ∀ f ∈ Fc, ∃ s ∈ K, f ⊆ s ∧ f.card = n + 1 := by
      intro f hf
      obtain ⟨s, hs, hfs⟩ := Finset.mem_biUnion.mp hf
      rcases Finset.mem_powersetCard.mp hfs with ⟨h1, h2⟩
      exact ⟨s, hs, h1, h2⟩
    have hswap : ∑ s ∈ K, (G.filter (fun f => f ⊆ s)).card
        = ∑ f ∈ G, (K.filter (fun s => f ⊆ s)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hL : ∀ s ∈ K, (G.filter (fun f => f ⊆ s)).card % 2
        = if s.image c = A then 1 else 0 := by
      intro s hs
      have hsc : s.card = n + 2 := hcards s hs
      have hEq : G.filter (fun f => f ⊆ s)
          = (s.powersetCard (s.card - 1)).filter (fun f => f.image c = B) := by
        ext f
        simp only [hG, Finset.mem_filter, Finset.mem_powersetCard, hsc]
        constructor
        · rintro ⟨⟨hfFc, himg⟩, hfs⟩
          obtain ⟨t, _, _, hcardf⟩ := hfacet_mem f hfFc
          exact ⟨⟨hfs, by omega⟩, himg⟩
        · rintro ⟨⟨hfs, hcardf⟩, himg⟩
          exact ⟨⟨Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_powersetCard.mpr ⟨hfs, by omega⟩⟩,
            himg⟩, hfs⟩
      rw [hEq]
      exact facet_parity c s A a ha (by omega) (Finset.card_pos.mp (by omega)) (hcolA s hs)
    have hR : ∀ f ∈ G, (K.filter (fun s => f ⊆ s)).card % 2
        = if f.biUnion carr ⊆ B then 1 else 0 := by
      intro f hf
      rcases Finset.mem_filter.mp hf with ⟨hfFc, himg⟩
      have hcarrA : f.biUnion carr ⊆ A := by
        intro x hx
        obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨s, hs, hfs, _⟩ := hfacet_mem f hfFc
        exact hcarr s hs v (hfs hv) hxv
      have hBsub : B ⊆ f.biUnion carr := by
        intro b hb
        have hbim : b ∈ f.image c := by rw [himg]; exact hb
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbim
        obtain ⟨s, hs, hfs, _⟩ := hfacet_mem f hfFc
        exact Finset.mem_biUnion.mpr ⟨v, hv, hc s hs v (hfs hv)⟩
      have hiff : (f.biUnion carr = A) ↔ ¬ (f.biUnion carr ⊆ B) := by
        constructor
        · intro h hsubB
          have hax : a ∈ B := hsubB (h ▸ ha)
          exact (Finset.mem_erase.mp hax).1 rfl
        · intro hnsub
          have hain : a ∈ f.biUnion carr := by
            by_contra hno
            exact hnsub (fun x hx => Finset.mem_erase.mpr ⟨fun h => hno (h ▸ hx), hcarrA hx⟩)
          apply Finset.Subset.antisymm hcarrA
          intro x hx
          by_cases hxa : x = a
          · rw [hxa]; exact hain
          · exact hBsub (Finset.mem_erase.mpr ⟨hxa, hx⟩)
      rw [hfacet f hfFc]
      by_cases hsubB : f.biUnion carr ⊆ B
      · rw [if_neg (fun h => (hiff.mp h) hsubB), if_pos hsubB]
      · rw [if_pos (hiff.mpr hsubB), if_neg hsubB]
    have hLsum : (∑ s ∈ K, (G.filter (fun f => f ⊆ s)).card) % 2
        = (K.filter (fun s => s.image c = A)).card % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl hL, ← Finset.card_filter]
    have hRsum : (∑ f ∈ G, (K.filter (fun s => f ⊆ s)).card) % 2
        = (G.filter (fun f => f.biUnion carr ⊆ B)).card % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl hR, ← Finset.card_filter]
    have hsubc : (subComplex K carr B (n + 1)).filter (fun f => f.image c = B)
        = G.filter (fun f => f.biUnion carr ⊆ B) := by
      rw [hG, subComplex, hFc, Finset.filter_filter, Finset.filter_filter]
      exact Finset.filter_congr (fun f _ => by tauto)
    have hIH : Odd (((subComplex K carr B (n + 1)).filter (fun f => f.image c = B)).card) := by
      refine ih B _ (hrec a ha) ?_
      intro f hf v hv
      have hfFc : f ∈ Fc := (Finset.mem_filter.mp hf).1
      obtain ⟨s, hs, hfs, _⟩ := hfacet_mem f hfFc
      exact hc s hs v (hfs hv)
    rw [Nat.odd_iff] at hIH ⊢
    rw [← hLsum, hswap, hRsum, ← hsubc]
    exact hIH

/-- Non-vacuity check: the simplex with vertex set `A`, taken as a single cell whose vertices
are the vertices of `A` itself (each carried by the corresponding vertex of the simplex),
is a triangulation in the sense of `Math.IsTriangulation`. -/
theorem isTriangulation_singleton :
    ∀ (n : ℕ) (A : Finset ℕ), A.card = n + 1 →
      IsTriangulation (V := ℕ) n A {A} (fun v => {v}) := by
  intro n
  induction n with
  | zero =>
    intro A hA
    refine ⟨hA, ⟨A, by simp⟩, by simp [hA], ?_, ?_⟩
    · intro s hs v hv
      rw [Finset.mem_singleton.mp hs] at hv
      simpa using hv
    · intro f hf
      simp only [facets, Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_powersetCard] at hf
      obtain ⟨s, rfl, hfs, hfc⟩ := hf
      have hf0 : f = ∅ := Finset.card_eq_zero.mp hfc
      subst hf0
      rw [if_neg (by simp only [Finset.biUnion_empty]; intro h; rw [← h] at hA; simp at hA)]
      rw [Finset.filter_singleton, if_pos (Finset.empty_subset _)]
      simp
  | succ n ih =>
    intro A hA
    refine ⟨hA, ⟨A, by simp⟩, by simp [hA], ?_, ?_, ?_⟩
    · intro s hs v hv
      rw [Finset.mem_singleton.mp hs] at hv
      simpa using hv
    · intro f hf
      simp only [facets, Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_powersetCard] at hf
      obtain ⟨s, rfl, hfs, hfc⟩ := hf
      have hne : f.biUnion (fun v => ({v} : Finset ℕ)) ≠ s := by
        rw [Finset.biUnion_singleton_eq_self]
        intro h; rw [h] at hfc; omega
      rw [if_neg hne, Finset.filter_singleton, if_pos hfs]
      simp
    · intro a ha
      have hcB : (A.erase a).card = n + 1 := by
        rw [Finset.card_erase_of_mem ha, hA]
        omega
      have hsub : subComplex (V := ℕ) {A} (fun v => {v}) (A.erase a) (n + 1) = {A.erase a} := by
        ext f
        simp only [subComplex, facets, Finset.mem_filter, Finset.mem_biUnion,
          Finset.mem_singleton, Finset.mem_powersetCard, Finset.biUnion_singleton_eq_self]
        constructor
        · rintro ⟨⟨s, rfl, hfs, hfc⟩, hsubB⟩
          exact Finset.eq_of_subset_of_card_le hsubB (by omega)
        · intro hfe
          subst hfe
          exact ⟨⟨A, rfl, Finset.erase_subset _ _, hcB⟩, Finset.Subset.refl _⟩
      rw [hsub]
      exact ih _ hcB

/-- The carrier function of a segment `[0,1]` subdivided at the midpoint: the vertex `0`
lies at the endpoint `0`, the vertex `2` at the endpoint `1`, and the vertex `1` in the
interior of the segment. -/
def segmentCarrier : ℕ → Finset ℕ := fun v => if v = 0 then {0} else if v = 1 then {0, 1} else {1}

/-- Non-vacuity check in a genuinely subdivided case: the segment `{0,1}` cut into the two
cells `{0,1}` and `{1,2}` is a triangulation in the sense of `Math.IsTriangulation`. -/
theorem isTriangulation_segment :
    IsTriangulation (V := ℕ) 1 {0, 1} {{0, 1}, {1, 2}} segmentCarrier := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro a ha
  fin_cases ha <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Existence form of Sperner's lemma**: a Sperner colouring of a triangulated simplex
admits at least one rainbow cell. -/
theorem exists_rainbow_cell (n : ℕ) (A : Finset ℕ) (K : Finset (Finset V))
    (carr : V → Finset ℕ) (c : V → ℕ)
    (hT : IsTriangulation n A K carr)
    (hc : ∀ s ∈ K, ∀ v ∈ s, c v ∈ carr v) :
    ∃ s ∈ K, s.image c = A := by
  obtain ⟨k, hk⟩ := sperner_lemma n A K carr c hT hc
  have hpos : 0 < (K.filter (fun s => s.image c = A)).card := by omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hs with ⟨hsK, hsimg⟩
  exact ⟨s, hsK, hsimg⟩

end Math

