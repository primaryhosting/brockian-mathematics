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

theorem shadow_image_image {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (𝒜 : Finset (Finset α)) :
    ∂ (𝒜.image (Finset.image f)) = (∂ 𝒜).image (Finset.image f) := by
  have h : Finset.image f = Finset.map ⟨f, hf⟩ := by
    funext s; rw [Finset.map_eq_image]; rfl
  rw [h, shadow_image_map]

/-- Being an initial segment of the colexicographic order is preserved by relabelling the ground
set along an order isomorphism. -/
