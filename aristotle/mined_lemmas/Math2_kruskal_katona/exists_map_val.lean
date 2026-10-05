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
