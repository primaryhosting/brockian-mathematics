import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` lines to precede any module doc comment, so the required
header appears immediately after the single `import Mathlib` line.)
-/

open Finset
open scoped FinsetFamily

namespace Math2

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Taking shadows commutes with pushing a family forward along an embedding. -/

lemma shadow_image_map (f : α ↪ β) (𝒜 : Finset (Finset α)) :
    ∂ (𝒜.image (Finset.map f)) = (∂ 𝒜).image (Finset.map f) := by
  ext t
  simp only [mem_shadow_iff, mem_image]
  constructor
  · rintro ⟨s', ⟨s, hs, rfl⟩, a, ha, rfl⟩
    rw [Finset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨s.erase b, ⟨s, hs, b, hb, rfl⟩, (Finset.map_erase f s b)⟩
  · rintro ⟨t', ⟨s, hs, b, hb, rfl⟩, rfl⟩
    exact ⟨s.map f, ⟨s, hs, rfl⟩, f b, Finset.mem_map_of_mem _ hb, (Finset.map_erase f s b).symm⟩

/-- Iterated shadows commute with pushing a family forward along an embedding. -/
