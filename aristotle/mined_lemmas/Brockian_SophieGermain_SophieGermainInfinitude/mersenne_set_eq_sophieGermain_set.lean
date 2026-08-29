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

theorem mersenne_set_eq_sophieGermain_set :
    {p : ℕ | p.Prime ∧ p % 4 = 3 ∧ (2 * p + 1) ∣ 2 ^ p - 1} =
      {p : ℕ | IsSophieGermainPrime p ∧ p % 4 = 3} := by
  ext p
  simp only [Set.mem_setOf_eq, IsSophieGermainPrime]
  constructor
  · rintro ⟨hp, h4, hd⟩
    exact ⟨⟨hp, prime_of_dvd_mersenne hp hd⟩, h4⟩
  · rintro ⟨⟨hp, hq⟩, h4⟩
    exact ⟨hp, h4, dvd_mersenne_of_safe_prime h4 hq⟩

/-- **Conditional reduction of the infinitude of Sophie Germain primes.**

The infinitude of Sophie Germain primes is a famous open problem, so it is established here in
a reduced (conditional) form: it suffices to exhibit arbitrarily large primes `p ≡ 3 [MOD 4]`
for which `2 * p + 1` divides the Mersenne number `2 ^ p - 1`.  Under that hypothesis the set
of Sophie Germain primes is infinite. -/
