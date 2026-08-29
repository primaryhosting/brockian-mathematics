import Mathlib

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace CS

/-- For `q` a prime factor of `n` with `q < n`, the product `∏_{i=1}^{q-1} (n - i)`
is not divisible by `q`. -/

theorem prime_iff_X_add_one_pow (n : ℕ) (hn : 2 ≤ n) :
    n.Prime ↔ ((X + 1 : (ZMod n)[X])) ^ n = X ^ n + 1 := by
  refine ⟨fun hp => ?_, fun h => by_contra fun hnp => not_congr_of_not_prime hn hnp h⟩
  have := (aks_primes_in_p n hn).mp hp 1 (Nat.coprime_one_left n)
  simpa using this

end CS

#print axioms CS.aks_primes_in_p
#print axioms CS.prime_iff_X_add_one_pow

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

