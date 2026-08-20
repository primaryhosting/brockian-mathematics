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
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/

theorem nonrainbow_case (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2)
    (hcol : ∀ v ∈ σ, c v < n + 2) (hne : σ.image c ≠ Finset.range (n + 2)) :
    (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card = 0 ∨
      (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card = 2 := by
  by_cases hsub : Finset.range (n + 1) ⊆ σ.image c
  · right
    have hnotmem : (n + 1) ∉ σ.image c := by
      intro hmem
      apply hne
      apply Finset.Subset.antisymm
      · intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨w, hw, rfl⟩ := hj
        exact Finset.mem_range.2 (hcol w hw)
      · intro j hj
        rw [Finset.mem_range] at hj
        rcases Nat.lt_or_ge j (n + 1) with h | h
        · exact hsub (Finset.mem_range.2 h)
        · have hj' : j = n + 1 := by omega
          rw [hj']; exact hmem
    have himg : σ.image c = Finset.range (n + 1) := by
      apply Finset.Subset.antisymm _ hsub
      intro j hj
      have hj2 : j < n + 2 := by
        rw [Finset.mem_image] at hj
        obtain ⟨w, hw, rfl⟩ := hj
        exact hcol w hw
      have : j ≠ n + 1 := fun h => hnotmem (h ▸ hj)
      exact Finset.mem_range.2 (by omega)
    have hkey : ∀ v ∈ σ, ((σ.erase v).image c = Finset.range (n + 1) ↔
        ∃ w ∈ σ, w ≠ v ∧ c w = c v) := by
      intro v hv
      constructor
      · intro h
        have hcv : c v ∈ Finset.range (n + 1) := by
          rw [← himg]; exact Finset.mem_image_of_mem c hv
        rw [← h, Finset.mem_image] at hcv
        obtain ⟨w, hw, hcw⟩ := hcv
        rw [Finset.mem_erase] at hw
        exact ⟨w, hw.2, hw.1, hcw⟩
      · rintro ⟨w, hwσ, hwv, hcw⟩
        apply Finset.Subset.antisymm
        · intro j hj
          rw [Finset.mem_image] at hj
          obtain ⟨u, hu, rfl⟩ := hj
          rw [← himg]
          exact Finset.mem_image_of_mem c (Finset.mem_of_mem_erase hu)
        · intro j hj
          rw [← himg, Finset.mem_image] at hj
          obtain ⟨u, hu, rfl⟩ := hj
          by_cases huv : u = v
          · subst huv
            exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwv, hwσ⟩, hcw⟩
          · exact Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩, rfl⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, hv₁₂, hc₁₂⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (t := Finset.range (n + 1)) (by rw [hσ, Finset.card_range]; omega)
        (fun a ha => by rw [← himg]; exact Finset.mem_image_of_mem c ha)
    have himg1 : (σ.erase v₁).image c = Finset.range (n + 1) :=
      (hkey v₁ hv₁).2 ⟨v₂, hv₂, hv₁₂.symm, hc₁₂.symm⟩
    have hinj1 : Set.InjOn c (σ.erase v₁) := by
      apply Finset.injOn_of_card_image_eq
      rw [himg1, Finset.card_erase_of_mem hv₁, hσ, Finset.card_range]
      omega
    have hfil : σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1)) = {v₁, v₂} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, hvi⟩
        obtain ⟨w, hwσ, hwv, hcw⟩ := (hkey v hv).1 hvi
        by_contra hcon
        push_neg at hcon
        obtain ⟨hvv₁, hvv₂⟩ := hcon
        by_cases hwv₁ : w = v₁
        · subst hwv₁
          exact hvv₂ (hinj1 (Finset.mem_erase.2 ⟨hvv₁, hv⟩)
            (Finset.mem_erase.2 ⟨hv₁₂.symm, hv₂⟩) (by rw [← hcw, hc₁₂]))
        · exact hwv (hinj1 (Finset.mem_erase.2 ⟨hwv₁, hwσ⟩)
            (Finset.mem_erase.2 ⟨hvv₁, hv⟩) hcw)
      · intro h
        rcases h with h | h
        · rw [h]; exact ⟨hv₁, himg1⟩
        · rw [h]; exact ⟨hv₂, (hkey v₂ hv₂).2 ⟨v₁, hv₁, hv₁₂, hc₁₂⟩⟩
    rw [hfil, Finset.card_insert_of_notMem (by simpa using hv₁₂), Finset.card_singleton]
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv h
    exact hsub (h ▸ Finset.image_subset_image (Finset.erase_subset v σ))

/-- A cell of dimension `n+1` contains an odd number of doors iff it is rainbow. -/
