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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime.
Landau's fourth problem asserts that this set is infinite; it is open. -/

theorem even_of_prime_sq_add_one {n : ℕ} (hn : 1 < n) (hp : Nat.Prime (n ^ 2 + 1)) : Even n := by
  rcases Nat.even_or_odd n with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := h
    have h2 : 2 ∣ n ^ 2 + 1 := ⟨2 * k ^ 2 + 2 * k + 1, by subst hk; ring⟩
    have hcases := hp.eq_one_or_self_of_dvd 2 h2
    have hbig : 4 < n ^ 2 + 1 := by nlinarith
    omega

/-- A sharper sieve condition: it suffices to rule out prime divisors `p ≤ n` that are
congruent to `1` modulo `4`, for even `n`. -/
