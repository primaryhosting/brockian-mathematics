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

theorem fortunate_prime_or_sq_le (n : ℕ) :
    Nat.Prime (fortunate n) ∨ (n + 1) ^ 2 ≤ fortunate n := by
  by_cases h : Nat.Prime (fortunate n)
  · exact Or.inl h
  refine Or.inr ?_
  have hpos : 0 < fortunate n := lt_trans Nat.zero_lt_one (one_lt_fortunate n)
  have hne : fortunate n ≠ 1 := (one_lt_fortunate n).ne'
  have hqp : Nat.Prime (fortunate n).minFac := Nat.minFac_prime hne
  have hlt : n < (fortunate n).minFac :=
    lt_of_prime_dvd_fortunate hqp (Nat.minFac_dvd _)
  calc (n + 1) ^ 2 ≤ (fortunate n).minFac ^ 2 := Nat.pow_le_pow_left hlt 2
    _ ≤ fortunate n := Nat.minFac_sq_le_self hpos h

/-- The Fortunate number of `0` is `2` (the primorial of `0` is `1`, and `1 + 2 = 3` is prime). -/
