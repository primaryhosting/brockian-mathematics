import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma coe_monoFinset (D : ℕ) :
    ((monoFinset F n D : Finset (Cube n → F)) : Set (Cube n → F))
      = {f | ∃ S : Finset (Fin n), S.card ≤ D ∧ f = mono F S} := by
  classical
  ext f
  constructor
  · intro hf
    simp only [monoFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter] at hf
    obtain ⟨S, hS, rfl⟩ := hf
    exact ⟨S, hS.2, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    simp only [monoFinset, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
    exact ⟨S, ⟨Finset.mem_univ _, hS⟩, rfl⟩

