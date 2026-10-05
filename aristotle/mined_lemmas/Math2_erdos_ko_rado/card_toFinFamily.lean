/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
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

/-- The family of subsets of `Fin n` corresponding to a family `F` of subsets of `[n]`. -/

private lemma card_toFinFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ F, A ⊆ Finset.range n) :
    (toFinFamily n F).card = F.card := by
  refine Finset.card_bij (fun s _ => s.map Fin.valEmbedding) ?_ ?_ ?_
  · intro s hs
    exact mem_toFinFamily.mp (Finset.mem_coe.mp hs)
  · intro s hs t ht hst
    exact Finset.map_injective _ hst
  · intro A hA
    have hA' : ∀ a ∈ A, a < n := fun a ha => Finset.mem_range.mp (hsub A hA ha)
    have hmap : (A.attachFin hA').map Fin.valEmbedding = A := by
      ext a
      simp only [Finset.mem_map, Fin.valEmbedding, Function.Embedding.coeFn_mk,
        Finset.mem_attachFin]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro ha
        exact ⟨⟨a, hA' a ha⟩, ha, rfl⟩
    exact ⟨A.attachFin hA', mem_toFinFamily.mpr (by rw [hmap]; exact hA), hmap⟩

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of
`[n] = {0, 1, …, n-1}` with `n ≥ 2k` has at most `C(n-1, k-1)` members. -/
