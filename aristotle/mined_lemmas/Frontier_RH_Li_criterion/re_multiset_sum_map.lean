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

lemma re_multiset_sum_map (Z : Multiset ℂ) (f : ℂ → ℂ) :
    ((Z.map f).sum).re = (Z.map (fun x => (f x).re)).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

