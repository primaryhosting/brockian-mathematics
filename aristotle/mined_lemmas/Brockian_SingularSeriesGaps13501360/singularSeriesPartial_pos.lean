/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

theorem singularSeriesPartial_pos {H : Finset ℤ} (hH : IsAdmissible H) (N : ℕ) :
    0 < singularSeriesPartial N H := by
  refine Finset.prod_pos fun p hp => singularFactor_pos hH ?_
  exact (Nat.mem_primesBelow.1 hp).2

/-- Explicit local factor of a pair at a prime not dividing the gap. -/
