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

theorem prime_of_prime_primorial_add_of_lt_sq {n m r : ℕ} (hm1 : 1 < m)
    (hp : Nat.Prime (primorial n + m)) (hgap : ∀ q : ℕ, Nat.Prime q → n < q → r ≤ q)
    (hlt : m < r ^ 2) : Nat.Prime m := by
  by_contra hmp
  have hqp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hq2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hmp
  have hqn : m.minFac ≤ n := by
    by_contra hc
    have : r ≤ m.minFac := hgap _ hqp (by omega)
    have : r ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left this 2
    omega
  exact not_dvd_of_prime_le hm1 hp hqp hqn (Nat.minFac_dvd m)

/-- **Fortune's conjecture, conditional reduction.**

Fortune's conjecture states that every fortunate number is prime; it is open.  The statement
below reduces it to the size bound saying that the fortunate number attached to `n#` is at
most `n ^ 2`.  (Fortunate numbers are conjecturally of size `O((log n)^2)`, far below `n ^ 2`,
so `hgap` is a very weak form of the expected prime-gap behaviour after primorials.) -/
