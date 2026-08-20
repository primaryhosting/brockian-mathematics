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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/

lemma ruthAaronSeed_twelve_six : RuthAaronSeed 12 6 := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
  rw [show (12 + 1 : ℕ) = 13 from rfl, show (12 : ℕ) = 2 * (2 * 3) from rfl,
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 13), sopfr_prime (by norm_num : Nat.Prime 3)]

/-- The Ruth–Aaron pair `(948, 949)` produced by the seed `a = 12, k = 6`:
`948 = 2^2 · 3 · 79` and `949 = 13 · 73`, both with prime factor sum `86`. -/
