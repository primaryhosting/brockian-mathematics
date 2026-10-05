/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open scoped FinsetFamily

namespace Math2

/-- Shadows commute with taking the image of a family along an injective map. -/

lemma shadow_image_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (𝒜 : Finset (Finset α)) :
    ∂ (𝒜.image (Finset.image f)) = (∂ 𝒜).image (Finset.image f) := by
  ext t
  simp only [mem_shadow_iff, mem_image]
  constructor
  · rintro ⟨S, ⟨s, hs, rfl⟩, b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    exact ⟨s.erase a, ⟨s, hs, a, ha, rfl⟩, Finset.image_erase hf s a⟩
  · rintro ⟨u, ⟨s, hs, a, ha, rfl⟩, rfl⟩
    exact ⟨s.image f, ⟨s, hs, rfl⟩, f a, mem_image_of_mem f ha, (Finset.image_erase hf s a).symm⟩

/-- Iterated shadows commute with taking the image of a family along an injective map. -/
