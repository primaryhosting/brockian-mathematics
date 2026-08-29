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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/

theorem prime_two_mul_add_one_iff_dvd_mersenne {p : ℕ} (hp : Nat.Prime p) (h4 : p % 4 = 3) :
    Nat.Prime (2 * p + 1) ↔ (2 * p + 1) ∣ 2 ^ p - 1 :=
  ⟨fun hq => dvd_mersenne_of_safe_prime h4 hq, fun hd => prime_of_dvd_mersenne hp hd⟩

/-- Equivalent reformulation of the problem restricted to `p ≡ 3 [MOD 4]`: the primes
`p ≡ 3 [MOD 4]` whose associated Mersenne number `2 ^ p - 1` is divisible by `2 * p + 1`
are exactly the Sophie Germain primes `p ≡ 3 [MOD 4]`. -/
