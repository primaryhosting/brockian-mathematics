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
