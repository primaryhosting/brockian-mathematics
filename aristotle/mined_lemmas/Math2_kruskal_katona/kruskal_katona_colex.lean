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
