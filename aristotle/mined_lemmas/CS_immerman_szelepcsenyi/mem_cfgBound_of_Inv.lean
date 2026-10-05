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

/-
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem mem_cfgBound_of_Inv (hs : s < N) {t : ℕ} (ht : t < N) {x : Cfg}
    (h : Inv N adj s t x) : x ∈ cfgBound N := by
  have hfil : ∀ i v : ℕ, ((R N adj s i).filter (fun y => y < v)).card ≤ N := fun i v =>
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (card_R_le hs i)
  cases x with
  | outer i c v k =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hk : k ≤ N := h5 ▸ hfil i v
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ ?_)))
      refine Finset.mem_image.2 ⟨(i, c, v, k), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | pathA i c v k p l =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hk : k ≤ N := h5 ▸ hfil i v
      have hp : p < N := by simpa using R_subset_range hs l h6
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ ?_)))
      refine Finset.mem_image.2 ⟨(i, c, v, k, p, l), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | inner i c v k d lb =>
      obtain ⟨h1, h2, h3, h4, h5, h6, S, hS, hScard, -⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hvk : v ≤ N ∧ k ≤ N := by
        rcases Nat.lt_or_ge N i with hi | hi
        · obtain ⟨hv, hk⟩ := h5 hi; exact ⟨by omega, by omega⟩
        · obtain ⟨hv, hk⟩ := h4 hi; exact ⟨by omega, hk ▸ hfil i v⟩
      have hd : d ≤ N := by
        rw [← hScard]
        exact le_trans (Finset.card_le_card (hS.trans (Finset.filter_subset _ _)))
          (card_R_le hs _)
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
      refine Finset.mem_image.2 ⟨(i, c, v, k, d, lb), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | pathB i c v k d u p l =>
      obtain ⟨h1, h2, h3, h4, h5, ⟨S, hS, hScard, -⟩, h7, h8, h9⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hvk : v ≤ N ∧ k ≤ N := by
        rcases Nat.lt_or_ge N i with hi | hi
        · obtain ⟨hv, hk⟩ := h5 hi; exact ⟨by omega, by omega⟩
        · obtain ⟨hv, hk⟩ := h4 hi; exact ⟨by omega, hk ▸ hfil i v⟩
      have hd : d ≤ N := by
        rw [← hScard]
        exact le_trans (Finset.card_le_card (hS.trans (Finset.filter_subset _ _)))
          (card_R_le hs _)
      have hp : p < N := by simpa using R_subset_range hs l h7
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_image.2 ⟨(i, c, v, k, d, u, p, l), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | acc => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **The space bound**: all configurations reachable by the complement machine lie in an
explicit set of size at most `5 * (N+2)^8`. -/
