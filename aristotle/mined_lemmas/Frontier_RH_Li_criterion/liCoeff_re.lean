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

lemma liCoeff_re (Z : Multiset ℂ) (n : ℕ) :
    (liCoeff Z n).re = (Z.map (fun ρ => 1 - ((1 - 1 / ρ) ^ n).re)).sum := by
  rw [liCoeff, re_multiset_sum_map]
  simp

/-- Reality of the Li coefficients for a multiset of zeros closed under complex conjugation. -/
