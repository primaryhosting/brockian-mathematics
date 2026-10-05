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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

open Finset

/-- The `n`-th repunit `R n = 1 + 10 + ... + 10^(n-1) = (10^n - 1)/9`, i.e. the number
whose decimal expansion consists of `n` ones. -/

theorem infinite_primes_dvd_repunit :
    {q : ℕ | q.Prime ∧ ∃ n : ℕ, 0 < n ∧ q ∣ repunit n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max N 3 + 1)
  have hp3 : 3 < p := by omega
  have hR : repunit p ≠ 1 := by
    have := one_lt_repunit (n := p) (by omega); omega
  set q := (repunit p).minFac with hqdef
  have hqp : q.Prime := Nat.minFac_prime hR
  have hqd : q ∣ repunit p := Nat.minFac_dvd _
  have hmod : q % (2 * p) = 1 := prime_factor_mod_two_mul hp hp3 hqp hqd
  have hlt : N < q := by
    have h1 : q % (2 * p) ≤ q := Nat.mod_le _ _
    rcases Nat.lt_or_ge q (2 * p) with hcase | hcase
    · rw [Nat.mod_eq_of_lt hcase] at hmod
      exact absurd hmod hqp.one_lt.ne'
    · have : N < 2 * p := by omega
      omega
  exact ⟨q, ⟨hqp, p, by omega, hqd⟩, hlt⟩

/-- The set of repunit primes is nonempty: `R 2 = 11` is prime. -/
