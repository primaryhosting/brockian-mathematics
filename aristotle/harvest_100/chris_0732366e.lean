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
lemma shadow_iterate_image_map_valEmbedding {n : ℕ} (i : ℕ) (ℬ : Finset (Finset (Fin n))) :
    ∂^[i] (ℬ.image (Finset.map Fin.valEmbedding))
      = (∂^[i] ℬ).image (Finset.map Fin.valEmbedding) := by
  induction i generalizing ℬ with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shadow_image_map_valEmbedding, ih]

/-- Every family of finite sets of naturals bounded by `n` comes from a family of subsets
of `Fin n`. -/
lemma exists_family_fin {𝒜 : Finset (Finset ℕ)} {n : ℕ} (h : ∀ s ∈ 𝒜, ∀ x ∈ s, x < n) :
    ∃ ℬ : Finset (Finset (Fin n)), ℬ.image (Finset.map Fin.valEmbedding) = 𝒜 := by
  classical
  refine ⟨Finset.univ.filter fun t : Finset (Fin n) ↦ t.map Fin.valEmbedding ∈ 𝒜, ?_⟩
  ext s
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    exact ⟨s.attachFin (h s hs), by rw [Finset.map_valEmbedding_attachFin]; exact hs,
      Finset.map_valEmbedding_attachFin _⟩

/-- The **Kruskal–Katona theorem** (Lovász form), for families of finite sets of naturals.

If every member of `𝒜` has size `r`, `i ≤ r ≤ k`, and `𝒜` has at least `k.choose r` members,
then the `i`-th iterated shadow of `𝒜` has at least `k.choose (r - i)` members.  Taking `i = 1`
gives the classical statement that a family of `r`-sets with at least `k.choose r` members has a
shadow with at least `k.choose (r - 1)` members. -/
theorem kruskal_katona {𝒜 : Finset (Finset ℕ)} {r k i : ℕ} (hir : i ≤ r) (hrk : r ≤ k)
    (h𝒜 : (𝒜 : Set (Finset ℕ)).Sized r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  classical
  set n : ℕ := max k ((𝒜.sup fun s ↦ s.sup id) + 1)
  have hbound : ∀ s ∈ 𝒜, ∀ x ∈ s, x < n := by
    intro s hs x hx
    have h1 : x ≤ s.sup id := Finset.le_sup (f := id) hx
    have h2 : s.sup id ≤ 𝒜.sup fun s ↦ s.sup id := Finset.le_sup hs
    have : x < (𝒜.sup fun s ↦ s.sup id) + 1 := Nat.lt_succ_of_le (h1.trans h2)
    exact this.trans_le (le_max_right _ _)
  have hkn : k ≤ n := le_max_left _ _
  obtain ⟨ℬ, hℬ⟩ := exists_family_fin hbound
  have hinj : Function.Injective (Finset.map (α := Fin n) Fin.valEmbedding) :=
    Finset.map_injective _
  have hℬsized : (ℬ : Set (Finset (Fin n))).Sized r := by
    intro t ht
    have : t.map Fin.valEmbedding ∈ 𝒜 := by
      rw [← hℬ]; exact Finset.mem_image_of_mem _ ht
    simpa using h𝒜 this
  have hcard' : k.choose r ≤ #ℬ := by
    rw [← hℬ, Finset.card_image_of_injective _ hinj] at hcard
    exact hcard
  have key := Finset.kruskal_katona_lovasz_form hir hrk hkn hℬsized hcard'
  have hshadow : #(∂^[i] 𝒜) = #(∂^[i] ℬ) := by
    rw [← hℬ, shadow_iterate_image_map_valEmbedding, Finset.card_image_of_injective _ hinj]
  rw [hshadow]; exact key

end Math2

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

