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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Nat

/-- Existence of a "fortunate offset": for every `n` there is some `m > 1` such that
`n# + m` is prime, where `n#` is the primorial of `n`.  This follows from Bertrand's
postulate applied to `n# + 1`. -/

theorem not_dvd_fortunate_of_prime_le {q n : ℕ} (hq : Nat.Prime q) (hqn : q ≤ n) :
    ¬ q ∣ fortunate n := by
  intro hdvd
  have hqP : q ∣ primorial n := prime_dvd_primorial hq hqn
  have hsum : q ∣ primorial n + fortunate n := Nat.dvd_add hqP hdvd
  have hP := prime_primorial_add_fortunate n
  have hq1 : q ≠ 1 := hq.ne_one
  have hqeq : q = primorial n + fortunate n := ((Nat.Prime.eq_one_or_self_of_dvd hP q hsum).resolve_left hq1)
  have hqle : q ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hqP
  have := one_lt_fortunate n
  omega

/-- Every prime factor of the Fortunate number of `n` is `> n`. -/
