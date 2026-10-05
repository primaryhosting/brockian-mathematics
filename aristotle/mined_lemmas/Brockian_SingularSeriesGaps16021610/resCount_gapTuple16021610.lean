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

theorem resCount_gapTuple16021610 :
    resCount gapTuple16021610 2 = 1 ∧ resCount gapTuple16021610 3 = 2 ∧
      resCount gapTuple16021610 5 = 4 ∧ resCount gapTuple16021610 7 = 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Modulo `2` the only class a set containing `1602` can miss is `1`. -/
