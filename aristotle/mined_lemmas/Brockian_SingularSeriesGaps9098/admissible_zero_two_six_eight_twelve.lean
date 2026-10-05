import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set of integer shifts `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series is
nonzero) when for every prime `p` the shifts miss at least one residue class
modulo `p`. -/

theorem admissible_zero_two_six_eight_twelve :
    Admissible ({0, 2, 6, 8, 12} : Finset ℤ) := by
  rw [admissible_iff_small_primes]
  intro p hp hple
  have hcard : ({0, 2, 6, 8, 12} : Finset ℤ).card = 5 := by decide
  rw [hcard] at hple
  have hp2 := hp.two_le
  interval_cases p
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact absurd hp (by decide)
  · exact ⟨4, by decide⟩

/-- Translates of an admissible set are admissible: admissibility depends only
on the pattern of gaps, not on where the range sits. -/
