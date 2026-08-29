import Mathlib

/-!
# Pair 11 13
Category: Frontier — Prime Numbers
Target: Twin.pair_11_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Twin

/-- **11 and 13 are twin primes**: both are prime and their difference is `2`.

The primality of each is obtained from the equivalent statement that no natural
number `m` with `2 ≤ m ≤ √n` divides `n` (`Nat.prime_def_le_sqrt`), which is a
finite check. -/
theorem pair_11_13 : Nat.Prime 11 ∧ Nat.Prime 13 ∧ 13 - 11 = 2 := by
  refine ⟨?_, ?_, rfl⟩
  · rw [Nat.prime_def_le_sqrt]
    refine ⟨by norm_num, ?_⟩
    intro m hm hms
    interval_cases m <;> omega
  · rw [Nat.prime_def_le_sqrt]
    refine ⟨by norm_num, ?_⟩
    intro m hm hms
    interval_cases m <;> omega

end Twin

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

