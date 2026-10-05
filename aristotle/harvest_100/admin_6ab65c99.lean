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
lemma shadow_iterate_image_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (i : ℕ) (𝒜 : Finset (Finset α)) :
    ∂^[i] (𝒜.image (Finset.image f)) = (∂^[i] 𝒜).image (Finset.image f) := by
  induction i generalizing 𝒜 with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shadow_image_of_injective hf, ih]

/-- **Kruskal–Katona theorem** (Lovász form), for families of finite sets of natural numbers.

If `𝒜` is a family of `r`-element subsets of `ℕ` with `#𝒜 ≥ k.choose r` (where `r ≤ k`), then for
every `i ≤ r` the `i`-th iterated shadow of `𝒜` has size at least `k.choose (r - i)`. -/
theorem kruskal_katona {i r k : ℕ} {𝒜 : Finset (Finset ℕ)} (hir : i ≤ r) (hrk : r ≤ k)
    (h𝒜 : (𝒜 : Set (Finset ℕ)).Sized r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(∂^[i] 𝒜) := by
  classical
  -- Every member of `𝒜` is contained in the union `U` of all members.
  set U : Finset ℕ := 𝒜.sup id with hU
  set n : ℕ := max k (U.sup id + 1) with hn
  have hkn : k ≤ n := le_max_left _ _
  have hlt : ∀ s ∈ 𝒜, ∀ m ∈ s, m < n := by
    intro s hs m hm
    have hmU : m ∈ U := mem_sup.2 ⟨s, hs, hm⟩
    have : m ≤ U.sup id := Finset.le_sup (f := id) hmU
    omega
  -- Transfer `𝒜` to a family of subsets of `Fin n`.
  set 𝒜' : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.image Fin.val ∈ 𝒜) with h𝒜'
  have hinj : Function.Injective (Fin.val : Fin n → ℕ) := Fin.val_injective
  have himg : 𝒜'.image (Finset.image (Fin.val : Fin n → ℕ)) = 𝒜 := by
    ext s
    simp only [h𝒜', mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨T, hT, rfl⟩; exact hT
    · intro hs
      exact ⟨s.attachFin (hlt s hs), by rw [Finset.image_val_attachFin]; exact hs,
        Finset.image_val_attachFin _⟩
  have hinj' : Function.Injective (Finset.image (Fin.val : Fin n → ℕ)) :=
    Finset.image_injective hinj
  have hcard' : #𝒜' = #𝒜 := by
    rw [← himg, Finset.card_image_of_injective _ hinj']
  have hsized : (𝒜' : Set (Finset (Fin n))).Sized r := by
    intro T hT
    have : T.image (Fin.val) ∈ 𝒜 := by
      simpa [h𝒜'] using hT
    have := h𝒜 this
    rwa [Finset.card_image_of_injective _ hinj] at this
  have key := Finset.kruskal_katona_lovasz_form hir hrk hkn hsized (by omega)
  have : #(∂^[i] 𝒜) = #(∂^[i] 𝒜') := by
    rw [← himg, shadow_iterate_image_of_injective hinj,
      Finset.card_image_of_injective _ hinj']
  omega

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

