/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently (by the Euler-product formula for
the singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`), the singular series attached
to `H` is non-zero, so that the Hardy–Littlewood prime `k`-tuple conjecture predicts infinitely
many translates of `H` consisting entirely of primes. -/

theorem card_le_four_of_admissible (H : Finset ℤ) (hsub : H ⊆ Finset.Icc (1602 : ℤ) 1610)
    (hadm : Admissible H) (hlo : (1602 : ℤ) ∈ H) (hhi : (1610 : ℤ) ∈ H) :
    H.card ≤ 4 := by
  have := Finset.card_le_card (subset_gapTuple_of_admissible H hsub hadm hlo hhi)
  rwa [card_gapTuple16021610] at this

/-- **Singular Series Gaps 16021610.**  The `4`-tuple `{1602, 1604, 1608, 1610}` is admissible:
no prime `p` has all of its residue classes covered by the tuple (so its singular series is
non-zero).  Moreover the tuple lies in, and spans, the gap range `[1602, 1610]`, exhibiting an
admissible prime constellation of diameter `8`, and it is the largest such configuration: every
admissible subset of `[1602, 1610]` containing both endpoints is contained in it. -/
