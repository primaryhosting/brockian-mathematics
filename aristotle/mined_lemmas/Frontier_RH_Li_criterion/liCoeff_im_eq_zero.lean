/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Filter Metric

namespace Frontier

/-- The `n`-th Li coefficient attached to a (finite) multiset `Z` of "zeros":
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/

lemma liCoeff_im_eq_zero (Z : Multiset ℂ) (hconj : Z.map (starRingEnd ℂ) = Z) (n : ℕ) :
    (liCoeff Z n).im = 0 := by
  have h : (starRingEnd ℂ) (liCoeff Z n) = liCoeff Z n := by
    rw [liCoeff, map_multiset_sum, Multiset.map_map]
    have hcomp : ((starRingEnd ℂ) ∘ fun ρ => 1 - (1 - 1 / ρ) ^ n)
        = (fun ρ => 1 - (1 - 1 / ρ) ^ n) ∘ (starRingEnd ℂ) := by
      funext ρ; simp
    rw [hcomp, ← Multiset.map_map, hconj]
  exact Complex.conj_eq_iff_im.mp h

/-- The Möbius transform `ρ ↦ 1 - 1/ρ` sends the closed half plane `Re ρ ≥ 1/2`
onto the closed unit disc. -/
