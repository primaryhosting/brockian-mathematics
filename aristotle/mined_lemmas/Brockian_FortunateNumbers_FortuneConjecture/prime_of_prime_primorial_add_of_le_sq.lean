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

/-- `IsFortunate n m` says that `m` is the *fortunate number* attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/

theorem prime_of_prime_primorial_add_of_le_sq {n m : ℕ} (hm1 : 1 < m)
    (hp : Nat.Prime (primorial n + m)) (hle : m ≤ n ^ 2) : Nat.Prime m := by
  by_contra hmp
  have hqp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
  have hqn : m.minFac ≤ n := by
    by_contra hc
    have : n ^ 2 < m.minFac ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  exact not_dvd_of_prime_le hm1 hp hqp hqn (Nat.minFac_dvd m)

/-- A sharper version of `prime_of_prime_primorial_add_of_le_sq`: it suffices that `m < r ^ 2`
where `r` is any prime with the property that there is no prime in the interval `(n, r)`
(e.g. `r` the least prime exceeding `n`). -/
