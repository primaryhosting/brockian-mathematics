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

lemma isRuthAaronPair_sevenHundredFourteen : IsRuthAaronPair 714 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (714 : ℕ) = 2 * (3 * (7 * 17)) from rfl,
    show (714 + 1 : ℕ) = 5 * (11 * 13) from rfl,
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 3) (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 7) (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 5) (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 11) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 17), sopfr_prime (by norm_num : Nat.Prime 13)]

end Brockian.RuthAaronPairs

#print axioms Brockian.RuthAaronPairs.RuthAaronInfinitude
#print axioms Brockian.RuthAaronPairs.isRuthAaronPair_of_seed
#print axioms Brockian.RuthAaronPairs.isRuthAaronPair_948

