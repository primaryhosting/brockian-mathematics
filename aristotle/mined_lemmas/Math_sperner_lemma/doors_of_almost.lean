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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of cells of `K` that contain the face `τ`. -/

theorem doors_of_almost (c : V → ℕ) (n : ℕ) (σ : Finset V) (hcard : σ.card = n + 2)
    (himg : σ.image c = range (n + 1)) : (doorsOf c n σ).card = 2 := by
  rw [doorsOf, card_filter_powersetCard_pred σ _ (n + 1) hcard]
  have hlt : (σ.image c).card < σ.card := by
    rw [himg, hcard, Finset.card_range]; omega
  obtain ⟨x, hx, y, hy, hne, hcxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun a ha => Finset.mem_image_of_mem c ha)
  have hdup : ∀ z ∈ σ, ∀ w ∈ σ, w ≠ z → c w = c z → (σ.erase z).image c = σ.image c := by
    intro z _ w hw hwz hcw
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
    · intro k hk
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hk
      by_cases huz : u = z
      · subst huz
        exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwz, hw⟩, hcw⟩
      · exact Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨huz, hu⟩, rfl⟩
  have hfilter : σ.filter (fun z => (σ.erase z).image c = range (n + 1)) = {x, y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hez⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨hzx, hzy⟩ := hcon
      have hxe : x ∈ σ.erase z := Finset.mem_erase.2 ⟨fun h => hzx h.symm, hx⟩
      have hye : y ∈ σ.erase z := Finset.mem_erase.2 ⟨fun h => hzy h.symm, hy⟩
      have hcard' : (σ.erase z).card = n + 1 := by
        rw [Finset.card_erase_of_mem hz, hcard]
        omega
      have hinj : Set.InjOn c (σ.erase z) := by
        apply Finset.injOn_of_card_image_eq
        rw [hez, hcard', Finset.card_range]
      exact hne (hinj hxe hye hcxy)
    · rintro (rfl | rfl)
      · exact ⟨hx, (hdup z hx y hy (fun h => hne h.symm) hcxy.symm).trans himg⟩
      · exact ⟨hy, (hdup z hy x hx hne hcxy).trans himg⟩
  rw [hfilter, Finset.card_pair hne]

omit [DecidableEq V] in
/-- A cell missing one of the colours `{0, …, n}` has no door. -/
