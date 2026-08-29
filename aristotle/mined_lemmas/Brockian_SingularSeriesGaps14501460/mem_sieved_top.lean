/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- A finite set of nonnegative integers is *admissible* (in the Hardy–Littlewood /
Hensley–Richards sense) if for every prime `p` it fails to cover all residue classes
modulo `p`.  Equivalently, the singular series attached to the tuple is nonzero. -/

theorem mem_sieved_top (q0 d : ℕ) (h : ∀ p ∈ smallPrimes, (q0 + d) % p ≠ 0) :
    d ∈ sieved q0 d :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩

/-- **Singular series gaps in the range 1450–1460.**

For a gap `d` with `1450 ≤ d ≤ 1460`, there exists an admissible tuple of at least `100`
elements whose smallest element is `0` and whose largest element is `d` (i.e. an admissible
tuple of diameter exactly `d`) **if and only if** `d` is even.

The forward implication is the parity obstruction modulo `2`; the reverse implication is
witnessed, for each of the six even values, by an explicit sieved window. -/
