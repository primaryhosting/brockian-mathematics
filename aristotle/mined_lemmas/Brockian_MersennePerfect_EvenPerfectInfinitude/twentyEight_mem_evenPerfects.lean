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

import Mathlib

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-! ## The Euclid–Euler theorem

The proofs in this section follow the classical Euclid–Euler argument (as formalized in
`Archive/Wiedijk100Theorems/PerfectNumbers.lean` in mathlib, which is not available as an
import here). -/


theorem twentyEight_mem_evenPerfects : (28 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)]
  decide

/-- `2` is a Mersenne exponent: `2 ^ 2 - 1 = 3` is prime. -/
