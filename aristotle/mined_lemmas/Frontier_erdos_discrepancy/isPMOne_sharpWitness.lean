/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

namespace Frontier

/-- The discrepancy sum of the sequence `f` along the homogeneous arithmetic progression
of common difference `d` and length `n`, i.e. `f d + f (2 d) + ... + f (n d)`. -/

lemma isPMOne_sharpWitness : IsPMOne sharpWitness := by
  intro n _
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
  | (k + 12) => left; rfl

/-- The bound `12` in `Frontier.erdos_discrepancy` is optimal: there is a `±1` sequence
all of whose homogeneous-progression discrepancies using indices at most `11` are `≤ 1`. -/
