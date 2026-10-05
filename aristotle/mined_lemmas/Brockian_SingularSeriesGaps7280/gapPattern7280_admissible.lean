import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when, for every prime `p`, the elements of `H` do not cover
all residue classes modulo `p`; equivalently the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime. -/

theorem gapPattern7280_admissible : Admissible gapPattern7280 := by
  rw [admissible_iff_small_primes, gapPattern7280_card]
  intro p hp hple
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

/--
**Singular Series Gaps 7280.**

A packaged admissibility ("nonvanishing singular series") statement for prime gap ranges:

1. the admissibility condition at a prime `p` is automatic once `p` exceeds `|H|`, so
   admissibility is decided by the finitely many primes `p ≤ |H|`;
2. admissibility is a translation-invariant property of the gap pattern, so each admissible
   pattern yields a whole family of admissible gap ranges `[t, t + diam]`;
3. the explicit pattern `{0, 2, 6, 8, 12, 18, 20, 26}` — eight points inside a range of
   length `26` — is admissible, and hence so is every translate of it.
-/
