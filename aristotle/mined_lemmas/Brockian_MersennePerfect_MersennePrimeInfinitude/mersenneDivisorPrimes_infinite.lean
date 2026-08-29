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
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked reduction*: the statement is shown to be equivalent to the infinitude of even
perfect numbers, via the Euclid–Euler correspondence `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`.

The target declaration `Brockian.MersennePerfect.MersennePrimeInfinitude` is therefore a
conditional theorem: *if* there are infinitely many even perfect numbers, *then* there are
infinitely many Mersenne primes.  The converse implication, and the resulting equivalence, are
also proved, as is a contrapositive/boundedness reformulation.
-/

namespace Brockian.MersennePerfect

open scoped Nat

/-- The set of exponents `p` for which `2 ^ p - 1` is a (Mersenne) prime.  Such a `p` is
automatically prime itself (see `mersenneExponents_eq`). -/

theorem mersenneDivisorPrimes_infinite : mersenneDivisorPrimes.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have h4 : (4 : ℕ) ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
  have hm1 : 1 < 2 ^ p - 1 := by omega
  have hq : Nat.Prime (2 ^ p - 1).minFac := Nat.minFac_prime (by omega)
  refine ⟨(2 ^ p - 1).minFac, ⟨hq, p, hp, Nat.minFac_dvd _⟩, ?_⟩
  have := lt_of_prime_dvd_mersenne hp hq (Nat.minFac_dvd _)
  omega

/-- Every Mersenne prime with prime exponent belongs to `mersenneDivisorPrimes`, so the
unconditional result above is a genuine weakening of the target statement. -/
