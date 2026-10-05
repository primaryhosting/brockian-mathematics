/-
Companion file to `RequestProject.FurstenbergSzemeredi`.

Here we prove the *converse* reduction: if every subset of `ℕ` of positive upper density
contains arithmetic progressions of length `k`, then the finitary Szemerédi property
`SzemerediFinitaryAt k` holds.  Consequently the hypothesis used in
`Frontier.furstenberg_szemeredi` is exactly equivalent to its conclusion, so the reduction
is lossless.

The proof is by contraposition: from a family of progression-free subsets of `[0, M)` of
density `≥ δ` with `M` arbitrarily large, we build a single set of positive upper density
with no progression of length `k`, by placing the `j`-th example in the interval
`[2 Lⱼ, 3 Lⱼ)` with the lengths `Lⱼ` growing at least geometrically with ratio `300`.
-/

import Mathlib
import RequestProject.FurstenbergSzemeredi

namespace Frontier

open scoped Classical

section Converse

variable (Mf : ℕ → ℕ) (Sf : ℕ → Finset ℕ)

/-- The thresholds used to select the successive blocks. -/

theorem hasPosUpperDensity_blockUnion {δ : ℝ} (hδ : 0 < δ) (hM : ∀ N, N ≤ Mf N)
    (hSub : ∀ N, Sf N ⊆ Finset.range (Mf N))
    (hCard : ∀ N, δ * (Mf N : ℝ) ≤ ((Sf N).card : ℝ)) :
    HasPosUpperDensity (blockUnion Mf Sf) := by
  refine ⟨δ / 3, by positivity, fun N => ?_⟩
  refine ⟨3 * blockLen Mf N, ?_, ?_⟩
  · have := self_le_blockLen hM N
    omega
  · have hcard_image : (blockSet Mf Sf N).card = (Sf (blockArg Mf N)).card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      simpa using hxy
    have hsub : blockSet Mf Sf N ⊆
        (Finset.range (3 * blockLen Mf N)).filter (fun n => n ∈ blockUnion Mf Sf) := by
      intro x hx
      have hb := blockSet_bounds hSub hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb.2, ?_⟩
      exact (mem_blockUnion_iff x).mpr ⟨N, hx⟩
    have h1 : ((blockSet Mf Sf N).card : ℝ) ≤
        ((((Finset.range (3 * blockLen Mf N)).filter
          (fun n => n ∈ blockUnion Mf Sf)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : δ * (blockLen Mf N : ℝ) ≤ ((blockSet Mf Sf N).card : ℝ) := by
      rw [hcard_image]
      exact hCard (blockArg Mf N)
    have h3 : δ / 3 * ((3 * blockLen Mf N : ℕ) : ℝ) = δ * (blockLen Mf N : ℝ) := by
      push_cast; ring
    rw [h3]
    linarith

/-- The constructed set contains no arithmetic progression of length `k` (for `k ≥ 3`). -/
