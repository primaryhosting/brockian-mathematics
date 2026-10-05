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

theorem missed_class_three (r : ZMod 3) (ha : ((1602 : ℤ) : ZMod 3) ≠ r)
    (hb : ((1610 : ℤ) : ZMod 3) ≠ r) : r = 1 := by
  revert ha hb; revert r; decide

/-- Optimality of the gap range: *any* admissible set contained in the interval `[1602, 1610]`
and containing both endpoints is a subset of `{1602, 1604, 1608, 1610}`.  Indeed the prime `2`
forces all elements to be even, and the prime `3` forces all elements to avoid the class
`1 mod 3`, which rules out `1606`. -/
