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

set_option grind.warning false

namespace Math2

open Finset
open scoped FinsetFamily

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pushing a family of finsets forward along an injection commutes with taking the shadow. -/
lemma shadow_image_map (f : α ↪ β) (𝒜 : Finset (Finset α)) :
    ∂ (𝒜.image (Finset.map f)) = (∂ 𝒜).image (Finset.map f) := by
  ext t
  simp only [Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_shadow_iff.1 ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    exact ⟨u.erase b, Finset.mem_shadow_iff.2 ⟨u, hu, b, hb, rfl⟩, Finset.map_erase f u b⟩
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨u, hu, b, hb, rfl⟩ := Finset.mem_shadow_iff.1 ht'
    refine Finset.mem_shadow_iff.2 ⟨u.map f, Finset.mem_image.2 ⟨u, hu, rfl⟩, f b,
      Finset.mem_map_of_mem _ hb, (Finset.map_erase f u b).symm⟩

/-- Iterated version of `Math2.shadow_image_map`. -/
lemma shadow_iterate_image_map (f : α ↪ β) (i : ℕ) (𝒜 : Finset (Finset α)) :
    ∂^[i] (𝒜.image (Finset.map f)) = (∂^[i] 𝒜).image (Finset.map f) := by
  induction i generalizing 𝒜 with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, shadow_image_map, ih]

/-- Every finset of naturals bounded by `n` comes from a finset of `Fin n`. -/
lemma exists_map_val {n : ℕ} (s : Finset ℕ) (h : ∀ m ∈ s, m < n) :
    ∃ t : Finset (Fin n), t.map ⟨Fin.val, Fin.val_injective⟩ = s := by
  refine ⟨s.attachFin h, ?_⟩
  ext a
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_attachFin]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact hb
  · intro ha; exact ⟨⟨a, h a ha⟩, ha, rfl⟩

/-- **The Kruskal–Katona theorem** (Lovász form), over the ground set `ℕ`.

If `𝒜` is a family of `r`-element sets of naturals with at least `k.choose r` members
(where `r ≤ k`), then for every `i ≤ r` the `i`-th iterated shadow of `𝒜` has at least
`k.choose (r - i)` members.

This is the sharp lower bound on shadow sizes: it is attained by the family of all `r`-subsets
of a `k`-element set. -/
theorem kruskal_katona {r k i : ℕ} {𝒜 : Finset (Finset ℕ)} (hir : i ≤ r) (hrk : r ≤ k)
    (h𝒜 : ∀ s ∈ 𝒜, #s = r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  classical
  -- Choose an ambient bound `n` for all the elements appearing in `𝒜`, with `k ≤ n`.
  set N : ℕ := (𝒜.sup id).sup id with hN
  set n : ℕ := max k (N + 1) with hn
  have hkn : k ≤ n := le_max_left _ _
  have hbound : ∀ s ∈ 𝒜, ∀ m ∈ s, m < n := by
    intro s hs m hm
    have h1 : s ≤ 𝒜.sup id := Finset.le_sup (f := id) hs
    have h2 : m ∈ 𝒜.sup id := h1 hm
    have h3 : m ≤ N := Finset.le_sup (f := id) h2
    exact lt_of_le_of_lt h3 (by omega)
  -- Transport `𝒜` to a family of finsets of `Fin n`.
  set e : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩ with he
  set ℬ : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powerset).filter (fun t => t.map e ∈ 𝒜) with hℬ
  have hmapinj : Function.Injective (Finset.map e) := Finset.map_injective e
  have hℬ𝒜 : ℬ.image (Finset.map e) = 𝒜 := by
    ext s
    simp only [Finset.mem_image, hℬ, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨t, ⟨-, ht⟩, rfl⟩; exact ht
    · intro hs
      obtain ⟨t, ht⟩ := exists_map_val (n := n) s (hbound s hs)
      exact ⟨t, ⟨Finset.subset_univ _, by rw [ht]; exact hs⟩, ht⟩
  have hℬsized : (ℬ : Set (Finset (Fin n))).Sized r := by
    intro t ht
    have : t.map e ∈ 𝒜 := by
      rw [← hℬ𝒜]; exact Finset.mem_image.2 ⟨t, ht, rfl⟩
    simpa using h𝒜 _ this
  have hℬcard : k.choose r ≤ #ℬ := by
    rwa [← hℬ𝒜, Finset.card_image_of_injective _ hmapinj] at hcard
  have := Finset.kruskal_katona_lovasz_form hir hrk hkn hℬsized hℬcard
  rwa [← hℬ𝒜, shadow_iterate_image_map, Finset.card_image_of_injective _ hmapinj]

end Math2

