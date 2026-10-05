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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- The `n`-th prime (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

theorem prime_of_lt_sq_nthPrime_succ {n m : ℕ} (hm : 1 < m)
    (hprime : (primorialOf n + m).Prime) (hlt : m < nthPrime (n + 1) ^ 2) : m.Prime := by
  by_contra hcomp
  have hq : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hcomp
  have hqlt : m.minFac < nthPrime (n + 1) := by
    by_contra hcon
    push_neg at hcon
    have : nthPrime (n + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hcon 2
    omega
  have hbig := nthPrime_lt_of_prime_dvd hm hprime hq (Nat.minFac_dvd m)
  exact absurd (le_nthPrime_of_lt_nthPrime_succ hq hqlt) (not_le.2 hbig)

/-- There is always some `m > 1` with `pₙ# + m` prime. -/
