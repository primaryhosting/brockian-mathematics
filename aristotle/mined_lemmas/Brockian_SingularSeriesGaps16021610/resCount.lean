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

def resCount (H : Finset ℤ) (p : ℕ) : ℕ := (H.image (fun h : ℤ => (h : ZMod p))).card

/-- Admissibility is exactly the statement that every local factor `1 - ν_p(H)/p` of the
singular series is non-zero, i.e. `ν_p(H) < p` for all primes `p`. -/
