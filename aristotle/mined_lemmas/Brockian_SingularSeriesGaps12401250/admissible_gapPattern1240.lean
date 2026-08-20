import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of nonnegative integer offsets (a "gap pattern") is *admissible* if for
every prime `p` the offsets fail to cover all residue classes modulo `p`.  Equivalently,
the singular series `𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` attached to `H` in the
Hardy–Littlewood prime `k`-tuple conjecture is nonzero. -/

theorem admissible_gapPattern1240 : Admissible gapPattern1240 := by
  apply admissible_of_small_primes
  intro p hp hple
  have hcard : gapPattern1240.card = 6 := by decide
  rw [hcard] at hple
  have h2 := hp.two_le
  interval_cases p <;> first
    | exact absurd hp (by decide)
    | (unfold gapPattern1240; decide)

