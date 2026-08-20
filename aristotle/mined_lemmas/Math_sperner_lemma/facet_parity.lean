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
