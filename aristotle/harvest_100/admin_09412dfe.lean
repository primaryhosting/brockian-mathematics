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
lemma shadow_iterate_image_map (f : α ↪ β) (𝒜 : Finset (Finset α)) (k : ℕ) :
    ∂^[k] (𝒜.image (Finset.map f)) = (∂^[k] 𝒜).image (Finset.map f) := by
  induction k generalizing 𝒜 with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shadow_image_map, ih]

/-- A family of finsets of naturals all of whose elements are `< n` is the pushforward of a
family of finsets of `Fin n`. -/
lemma exists_family_fin {n : ℕ} (𝒜 : Finset (Finset ℕ)) (h : ∀ s ∈ 𝒜, ∀ a ∈ s, a < n) :
    ∃ ℬ : Finset (Finset (Fin n)), ℬ.image (Finset.map Fin.valEmbedding) = 𝒜 := by
  classical
  refine ⟨(Finset.univ : Finset (Finset (Fin n))).filter
    (fun t => t.map Fin.valEmbedding ∈ 𝒜), ?_⟩
  ext s
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ht
  · intro hs
    exact ⟨s.attachFin (h s hs), by rw [Finset.map_valEmbedding_attachFin]; exact hs,
      Finset.map_valEmbedding_attachFin _⟩

/-- **The Kruskal–Katona theorem** (Lovász form), for families of finite sets of naturals.

If `𝒜` is a family of `r`-element sets of naturals with at least `k.choose r` members
(where `i ≤ r ≤ k`), then its `i`-th iterated shadow has at least `k.choose (r - i)` members. -/
theorem kruskal_katona {i r k : ℕ} {𝒜 : Finset (Finset ℕ)} (hir : i ≤ r) (hrk : r ≤ k)
    (h𝒜 : (𝒜 : Set (Finset ℕ)).Sized r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  classical
  set n : ℕ := max k (𝒜.sup (fun s => s.sup id) + 1) with hn
  have hkn : k ≤ n := le_max_left _ _
  have hlt : ∀ s ∈ 𝒜, ∀ a ∈ s, a < n := by
    intro s hs a ha
    have h1 : a ≤ s.sup id := Finset.le_sup (f := id) ha
    have h2 : s.sup id ≤ 𝒜.sup (fun s => s.sup id) := Finset.le_sup hs
    omega
  obtain ⟨ℬ, hℬ⟩ := exists_family_fin (n := n) 𝒜 hlt
  have hinj : Function.Injective (Finset.map (Fin.valEmbedding (n := n))) :=
    Finset.map_injective _
  have hcardB : #ℬ = #𝒜 := by
    rw [← hℬ, Finset.card_image_of_injective _ hinj]
  have hℬr : (ℬ : Set (Finset (Fin n))).Sized r := by
    intro t ht
    have : t.map Fin.valEmbedding ∈ 𝒜 := by
      rw [← hℬ]; exact Finset.mem_image_of_mem _ ht
    simpa using h𝒜 this
  have := Finset.kruskal_katona_lovasz_form (n := n) (i := i) (r := r) (k := k)
    hir hrk hkn hℬr (by omega)
  have heq : #(∂^[i] 𝒜) = #(∂^[i] ℬ) := by
    rw [← hℬ, shadow_iterate_image_map, Finset.card_image_of_injective _ hinj]
  omega

/-- The single-shadow form of the Kruskal–Katona theorem: a family of `r`-sets of naturals
(`1 ≤ r ≤ k`) with at least `k.choose r` members has shadow of size at least
`k.choose (r - 1)`. -/
theorem kruskal_katona_shadow {r k : ℕ} {𝒜 : Finset (Finset ℕ)} (hr : 1 ≤ r) (hrk : r ≤ k)
    (h𝒜 : (𝒜 : Set (Finset ℕ)).Sized r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - 1) ≤ #(∂ 𝒜) := by
  simpa using kruskal_katona hr hrk h𝒜 hcard

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

