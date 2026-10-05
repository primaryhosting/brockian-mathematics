/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

open Finset
open scoped FinsetFamily

/-- Shadows commute with relabelling the ground set along an embedding. -/
theorem shadow_image_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (𝒜 : Finset (Finset α)) : ∂ (𝒜.image (Finset.map f)) = (∂ 𝒜).image (Finset.map f) := by
  ext t
  simp only [mem_shadow_iff, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨u, hu, rfl⟩, a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    exact ⟨u.erase b, ⟨u, hu, b, hb, rfl⟩, by rw [Finset.map_erase]⟩
  · rintro ⟨s, ⟨u, hu, b, hb, rfl⟩, rfl⟩
    exact ⟨u.map f, ⟨u, hu, rfl⟩, f b, Finset.mem_map_of_mem _ hb, by rw [Finset.map_erase]⟩

/-- Iterated shadows commute with relabelling the ground set along an embedding. -/
theorem shadow_iterate_image_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (i : ℕ) (𝒜 : Finset (Finset α)) :
    ∂^[i] (𝒜.image (Finset.map f)) = (∂^[i] 𝒜).image (Finset.map f) := by
  induction i generalizing 𝒜 with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, shadow_image_map, ih]

/-- Shadows commute with relabelling the ground set along an injection. -/
theorem shadow_image_image {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (𝒜 : Finset (Finset α)) :
    ∂ (𝒜.image (Finset.image f)) = (∂ 𝒜).image (Finset.image f) := by
  have h : Finset.image f = Finset.map ⟨f, hf⟩ := by
    funext s; rw [Finset.map_eq_image]; rfl
  rw [h, shadow_image_map]

/-- Being an initial segment of the colexicographic order is preserved by relabelling the ground
set along an order isomorphism. -/
theorem isInitSeg_image {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ} (e : α ≃o Fin n)
    {𝒞 : Finset (Finset α)} {r : ℕ} (h : Finset.Colex.IsInitSeg 𝒞 r) :
    Finset.Colex.IsInitSeg (𝒞.image (Finset.image e)) r := by
  classical
  have hmono : StrictMono (e : α → Fin n) := e.strictMono
  constructor
  · rintro s hs
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Finset.card_image_of_injective _ e.injective]
    exact h.1 hu
  · rintro s t hs ⟨hlt, hcard⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hs
    have hid : ((e : α → Fin n) ∘ (e.symm : Fin n → α)) = id := funext fun x ↦ by simp
    refine Finset.mem_image.2 ⟨t.image (e.symm : Fin n → α), ?_, ?_⟩
    · refine h.2 hu ⟨?_, ?_⟩
      · rw [← Finset.Colex.toColex_image_lt_toColex_image hmono]
        rwa [Finset.image_image, hid, Finset.image_id]
      · rwa [Finset.card_image_of_injective _ e.symm.injective]
    · rw [Finset.image_image, hid, Finset.image_id]

/-- **The Kruskal–Katona theorem** (initial-segment form), on an arbitrary linearly ordered
finite ground set.

If `𝒜` is a family of `r`-sets and `𝒞` is an initial segment of the colexicographic order on
`r`-sets with `#𝒞 ≤ #𝒜`, then `#(∂ 𝒞) ≤ #(∂ 𝒜)`: the minimum shadow size among families of a
given size is attained by initial segments of colex. -/
theorem kruskal_katona_colex {α : Type*} [Fintype α] [LinearOrder α] {𝒜 𝒞 : Finset (Finset α)}
    {r : ℕ} (h𝒜 : (𝒜 : Set (Finset α)).Sized r) (h𝒞𝒜 : #𝒞 ≤ #𝒜)
    (h𝒞 : Finset.Colex.IsInitSeg 𝒞 r) : #(∂ 𝒞) ≤ #(∂ 𝒜) := by
  classical
  set e : α ≃o Fin (Fintype.card α) := (monoEquivOfFin α rfl).symm
  have hinj : Function.Injective (e : α → Fin (Fintype.card α)) := e.injective
  have himg : Function.Injective (Finset.image (e : α → Fin (Fintype.card α))) :=
    Finset.image_injective hinj
  have hsized : ((𝒜.image (Finset.image (e : α → Fin (Fintype.card α))) :
      Finset (Finset (Fin (Fintype.card α)))) : Set (Finset (Fin (Fintype.card α)))).Sized r := by
    rintro s hs
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Finset.card_image_of_injective _ hinj]
    exact h𝒜 hu
  have key := Finset.kruskal_katona hsized
    (by rwa [Finset.card_image_of_injective _ himg, Finset.card_image_of_injective _ himg])
    (isInitSeg_image e h𝒞)
  rwa [shadow_image_image hinj, shadow_image_image hinj,
    Finset.card_image_of_injective _ himg, Finset.card_image_of_injective _ himg] at key

/-- **The Kruskal–Katona theorem** (Lovász form), on an arbitrary finite ground set.

If `𝒜` is a family of `r`-element subsets of a finite type `α` with at least `k.choose r`
members (where `i ≤ r ≤ k ≤ card α`), then its `i`-th iterated shadow — the family of all
`(r - i)`-element sets contained in some member of `𝒜` — has at least `k.choose (r - i)`
members. Equivalently, initial segments of the colexicographic order minimise shadow sizes. -/
theorem kruskal_katona {α : Type*} [Fintype α] [DecidableEq α] {𝒜 : Finset (Finset α)}
    {r i k : ℕ} (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ Fintype.card α)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) (hk : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  classical
  set f : α ↪ Fin (Fintype.card α) := (Fintype.equivFin α).toEmbedding
  set 𝒜' : Finset (Finset (Fin (Fintype.card α))) := 𝒜.image (Finset.map f) with h𝒜'
  have hinj : Function.Injective (Finset.map f) := Finset.map_injective f
  have hcard : #𝒜' = #𝒜 := Finset.card_image_of_injective _ hinj
  have hsized : (𝒜' : Set (Finset (Fin (Fintype.card α)))).Sized r := by
    rintro s hs
    simp only [h𝒜', Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Finset.card_map]
    exact h𝒜 hu
  have key := Finset.kruskal_katona_lovasz_form hir hrk (by simpa using hkn) hsized (by omega)
  rwa [h𝒜', shadow_iterate_image_map, Finset.card_image_of_injective _ hinj] at key

/-- The single-shadow case of the Kruskal–Katona theorem: a family of `r`-sets with at least
`k.choose r` members has a shadow with at least `k.choose (r - 1)` members. -/
theorem kruskal_katona_shadow {α : Type*} [Fintype α] [DecidableEq α] {𝒜 : Finset (Finset α)}
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (hkn : k ≤ Fintype.card α)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) (hk : k.choose r ≤ #𝒜) :
    k.choose (r - 1) ≤ #(∂ 𝒜) := by
  simpa using kruskal_katona (i := 1) hr hrk hkn h𝒜 hk

end Math2

