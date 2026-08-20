/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - 1/p)^{-|H|} (1 - ν_p(H)/p)` is nonzero at every prime. -/

theorem gapTuple_admissible : Admissible gapTuple := by
  apply admissible_of_small_primes
  intro p hp hple
  rw [gapTuple_card] at hple
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨3, by decide⟩
  · exact absurd hp (by decide)

/-- **Singular Series Gaps 16021610.**
The pattern `H = {0, 2, 6, 8, 12, 18, 20, 26}` is an admissible `8`-tuple lying in the
gap range `[0, 26]` (with both endpoints attained), and every translate `H + n` of it is
again admissible.  Hence for each prime `p` the local factor `1 - ν_p(H)/p` of the
singular series `𝔖(H)` is nonzero, so the Hardy–Littlewood conjecture predicts infinitely
many translates of this range consisting of `8` primes. -/
