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

/-
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(A001414, the "integer logarithm"). By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem sopf_25 : sopf 25 = 5 := by
  have h : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [sopf, h, Nat.primeFactors_prime_pow (by norm_num) (by norm_num)]
  decide

/-- `(24, 25)` is a Ruth–Aaron pair for the sum of distinct prime factors:
`24 = 2^3·3` and `25 = 5^2` both give `5`. -/
