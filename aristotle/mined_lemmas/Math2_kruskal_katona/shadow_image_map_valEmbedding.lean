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

/-- Pushing a family of subsets of `Fin n` forward into `ℕ` commutes with taking shadows. -/

lemma shadow_image_map_valEmbedding {n : ℕ} (ℬ : Finset (Finset (Fin n))) :
    ∂ (ℬ.image (Finset.map Fin.valEmbedding))
      = (∂ ℬ).image (Finset.map Fin.valEmbedding) := by
  ext t
  simp only [Finset.mem_shadow_iff, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨u, hu, rfl⟩, a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    exact ⟨u.erase b, ⟨u, hu, b, hb, rfl⟩, Finset.map_erase _ _ _⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, b, hb, rfl⟩ := hv
    exact ⟨u.map Fin.valEmbedding, ⟨u, hu, rfl⟩, Fin.valEmbedding b,
      Finset.mem_map_of_mem _ hb, (Finset.map_erase _ _ _).symm⟩

/-- Iterated version of `shadow_image_map_valEmbedding`. -/
