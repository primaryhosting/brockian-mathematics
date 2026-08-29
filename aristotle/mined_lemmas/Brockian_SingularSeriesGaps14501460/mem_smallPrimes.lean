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

theorem mem_smallPrimes {p : ℕ} (hp : p.Prime) (hle : p ≤ 140) : p ∈ smallPrimes := by
  revert hp
  revert hle
  revert p
  decide

/-- The admissible tuple obtained by sieving the window `[q0, q0 + d]` by all primes
below `141`, translated back to start at `0`. -/
