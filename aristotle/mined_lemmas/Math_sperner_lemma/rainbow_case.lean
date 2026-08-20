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

theorem rainbow_case (c : V → ℕ) (n : ℕ) (σ : Finset V) (hσ : σ.card = n + 2)
    (himg : σ.image c = Finset.range (n + 2)) :
    (σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))).card = 1 := by
  have hinj : Set.InjOn c σ := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hσ, Finset.card_range]
  have herase : ∀ v ∈ σ, (σ.erase v).image c = (Finset.range (n + 2)).erase (c v) := by
    intro v hv
    ext j
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro ⟨w, ⟨hwv, hwσ⟩, rfl⟩
      refine ⟨fun h => hwv (hinj hwσ hv h), ?_⟩
      have hc : c w ∈ σ.image c := Finset.mem_image_of_mem c hwσ
      rw [himg, Finset.mem_range] at hc
      exact hc
    · rintro ⟨hj, hjlt⟩
      have hj' : j ∈ σ.image c := by rw [himg, Finset.mem_range]; exact hjlt
      rw [Finset.mem_image] at hj'
      obtain ⟨w, hw, rfl⟩ := hj'
      exact ⟨w, ⟨fun h => hj (by rw [h]), hw⟩, rfl⟩
  have hfilter : σ.filter (fun v => (σ.erase v).image c = Finset.range (n + 1))
      = σ.filter (fun v => c v = n + 1) := by
    apply Finset.filter_congr
    intro v hv
    rw [herase v hv]
    constructor
    · intro h
      by_contra hne
      have h1 : n + 1 ∈ (Finset.range (n + 2)).erase (c v) :=
        Finset.mem_erase.2 ⟨fun hh => hne hh.symm, Finset.mem_range.2 (by omega)⟩
      rw [h, Finset.mem_range] at h1
      omega
    · intro h
      rw [h]
      ext j
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
  rw [hfilter]
  have hn : (n + 1) ∈ σ.image c := by rw [himg, Finset.mem_range]; omega
  rw [Finset.mem_image] at hn
  obtain ⟨v₀, hv₀, hcv₀⟩ := hn
  rw [Finset.card_eq_one]
  refine ⟨v₀, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hcw⟩
    exact hinj hw hv₀ (by rw [hcw, hcv₀])
  · rintro rfl
    exact ⟨hv₀, hcv₀⟩

omit [Fintype V] in
/-- A non-rainbow cell has either no door or exactly two doors. -/
