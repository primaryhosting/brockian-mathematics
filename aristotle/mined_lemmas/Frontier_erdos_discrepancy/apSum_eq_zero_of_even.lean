/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression of common
difference `d`: `apSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`. -/

theorem apSum_eq_zero_of_even (f : ℕ → ℤ) (hf : IsPMOne f) (d : ℕ) (hd : 0 < d)
    (n : ℕ) (hn : Even n) (hbd : |apSum f d n| ≤ 1) : apSum f d n = 0 := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨k, hk⟩ := apSum_parity f hf d hd n
  rw [abs_le] at hbd
  subst hm
  push_cast at hk
  omega

/-- **Base case of the Erdős discrepancy problem** (`C = 1`).

Every `±1` sequence `f` has discrepancy at least `2` on homogeneous arithmetic
progressions: there are `d ≤ 3` and `n ≤ 10` with `|f d + f (2d) + ⋯ + f (nd)| ≥ 2`.
Equivalently, no `±1` sequence has discrepancy at most `1`. -/
