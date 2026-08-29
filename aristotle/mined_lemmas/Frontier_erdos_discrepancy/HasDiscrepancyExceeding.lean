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

/-- A `±1`-sequence: a function `f : ℕ → ℤ` taking only the values `1` and `-1`
on the positive integers. -/

def HasDiscrepancyExceeding (f : ℕ → ℤ) (C : ℤ) : Prop :=
  ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n|

/-- The Erdős discrepancy problem (solved by Tao, 2015): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions.  This is stated
here as a `Prop`-valued definition, recording the full statement; the theorem
`Frontier.erdos_discrepancy` below establishes its first nontrivial instance
`C = 1` (i.e. no `±1` sequence has discrepancy at most `1`). -/
