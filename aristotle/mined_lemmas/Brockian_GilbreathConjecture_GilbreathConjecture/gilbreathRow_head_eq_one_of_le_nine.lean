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

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem gilbreathRow_head_eq_one_of_le_nine {p : Nat → Nat} (hp : IsPrimeEnumeration p)
    (m : Nat) (h1 : 1 ≤ m) (h9 : m ≤ 9) : gilbreathRow p m 0 = 1 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm : m = 1 := by omega
    subst hm
    exact (isOdlyzko_row_one hp).1
  · obtain ⟨j, rfl⟩ : ∃ j, m = 2 + j := ⟨m - 2, by omega⟩
    rw [gilbreathRow_add]
    exact head_iterD_eq_one (isOdlyzko_row_two hp) (by omega)

end Brockian.GilbreathConjecture

import Mathlib
import Brockian.GilbreathConjecture

/-!
# The prime enumeration used by the Gilbreath triangle

`Brockian.GilbreathConjecture` is developed for an arbitrary increasing
enumeration `p` of the primes (`IsPrimeEnumeration p`).  Here we check, against
Mathlib, that such an enumeration exists — namely `Nat.nth Nat.Prime` — so that
the conditional reduction proved there is not vacuous, and we specialize it to
the primes.
-/

namespace Brockian.GilbreathConjecture

/-- The elementary primality predicate used in `Brockian.GilbreathConjecture`
agrees with Mathlib's `Nat.Prime`. -/
