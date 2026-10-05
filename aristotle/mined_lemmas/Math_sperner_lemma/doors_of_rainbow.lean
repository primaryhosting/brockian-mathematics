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

theorem doors_of_rainbow (c : V → ℕ) (n : ℕ) (σ : Finset V) (hcard : σ.card = n + 2)
    (himg : σ.image c = range (n + 2)) : (doorsOf c n σ).card = 1 := by
  rw [doorsOf, card_filter_powersetCard_pred σ _ (n + 1) hcard]
  have hinj : Set.InjOn c σ := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hcard, Finset.card_range]
  have hkey : ∀ x ∈ σ, ((σ.erase x).image c = range (n + 1) ↔ c x = n + 1) := by
    intro x hx
    constructor
    · intro he
      by_contra hne
      have hmem : (n + 1) ∈ σ.image c := by rw [himg]; simp
      obtain ⟨y, hy, hcy⟩ := Finset.mem_image.1 hmem
      have hyx : y ≠ x := by rintro rfl; exact hne hcy
      have hmem' : (n + 1) ∈ (σ.erase x).image c :=
        Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, hcy⟩
      rw [he] at hmem'
      simp at hmem'
    · intro hcx
      ext k
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range]
      constructor
      · rintro ⟨y, ⟨hyx, hy⟩, rfl⟩
        have h1 : c y ∈ range (n + 2) := by rw [← himg]; exact Finset.mem_image_of_mem c hy
        rw [Finset.mem_range] at h1
        have h2 : c y ≠ n + 1 := by
          rw [← hcx]; intro h; exact hyx (hinj hy hx h)
        omega
      · intro hk
        have hmem : k ∈ σ.image c := by rw [himg, Finset.mem_range]; omega
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hmem
        refine ⟨y, ⟨?_, hy⟩, rfl⟩
        rintro rfl
        omega
  rw [Finset.card_eq_one]
  have hmem : (n + 1) ∈ σ.image c := by rw [himg]; simp
  obtain ⟨x0, hx0, hcx0⟩ := Finset.mem_image.1 hmem
  refine ⟨x0, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hey⟩
    exact hinj hy hx0 (((hkey y hy).1 hey).trans hcx0.symm)
  · rintro rfl
    exact ⟨hx0, (hkey _ hx0).2 hcx0⟩

/-- A cell carrying exactly the colours `{0, …, n}` has exactly two doors. -/
