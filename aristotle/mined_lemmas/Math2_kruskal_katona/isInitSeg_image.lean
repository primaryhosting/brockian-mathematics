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
