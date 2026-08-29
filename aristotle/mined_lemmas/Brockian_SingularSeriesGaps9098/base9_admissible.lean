/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

namespace Brockian

/-- The number of residue classes modulo `p` occupied by a finite set `H` of natural numbers.
This is the quantity `ν_H(p)` appearing in the Euler factors of the Hardy–Littlewood
singular series of the tuple `H`. -/

theorem base9_admissible : Admissible base9 := by
  apply admissible_of_small_primes
  rw [base9_card]
  decide

/-- **Singular Series Gaps 9098.**

The `9`-element gap pattern `H = {0, 2, 6, 8, 12, 18, 20, 26, 30}` and *every* one of its
translates `H + n` is admissible: for each prime `p` some residue class mod `p` is omitted,
so the number of occupied classes satisfies `ν(p) < p` and each Euler factor
`1 - ν(p)/p` of the Hardy–Littlewood singular series is strictly positive.  Consequently the
pattern yields admissible gap ranges `[n, n+30]` starting at arbitrarily large `n`. -/
