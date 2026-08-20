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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Andrica's conjecture states that for every `n`,
`√(p_{n+1}) - √(p_n) < 1`, where `p_n` denotes the `n`-th prime.
This is an open problem, so the statement itself is recorded as a `Prop`
(`AndricaConjecture`), and what is proved here are:

* an exact reformulation as a bound on prime gaps (`andrica_iff_gap`,
  `andrica_iff_gap_lt`);
* a conditional reduction to a purely arithmetic gap bound
  (`andrica_of_natSqrt_gap`);
* an unconditional verification of the conjecture for the first 25 gaps
  (`andrica_of_lt_25`).

No lemma in Mathlib proves Andrica's conjecture. The Mathlib input used below
is `Nat.nth Nat.Prime` (the `n`-th prime, cf. `Nat.prime_nth_prime`,
`Nat.nth_count`) together with the `Real.sqrt` API
(`Real.sqrt_lt'`, `Real.sq_sqrt`, `Real.nat_sqrt_le_real_sqrt`).
-/

namespace Brockian.AndricaConjecture

open Real

/-- **Andrica's conjecture**: consecutive primes satisfy
`√(p_{n+1}) - √(p_n) < 1`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th
prime (indexed from `p_0 = 2`). -/

theorem andrica_of_lt_25 (n : ℕ) (hn : n < 25) :
    √(Nat.nth Nat.Prime (n + 1)) - √(Nat.nth Nat.Prime n) < 1 := by
  interval_cases n
  · exact andrica_at_of_values nth_prime_0 nth_prime_1 (by norm_num)
  · exact andrica_at_of_values nth_prime_1 nth_prime_2 (by norm_num)
  · exact andrica_at_of_values nth_prime_2 nth_prime_3 (by norm_num)
  · exact andrica_at_of_values nth_prime_3 nth_prime_4 (by norm_num)
  · exact andrica_at_of_values nth_prime_4 nth_prime_5 (by norm_num)
  · exact andrica_at_of_values nth_prime_5 nth_prime_6 (by norm_num)
  · exact andrica_at_of_values nth_prime_6 nth_prime_7 (by norm_num)
  · exact andrica_at_of_values nth_prime_7 nth_prime_8 (by norm_num)
  · exact andrica_at_of_values nth_prime_8 nth_prime_9 (by norm_num)
  · exact andrica_at_of_values nth_prime_9 nth_prime_10 (by norm_num)
  · exact andrica_at_of_values nth_prime_10 nth_prime_11 (by norm_num)
  · exact andrica_at_of_values nth_prime_11 nth_prime_12 (by norm_num)
  · exact andrica_at_of_values nth_prime_12 nth_prime_13 (by norm_num)
  · exact andrica_at_of_values nth_prime_13 nth_prime_14 (by norm_num)
  · exact andrica_at_of_values nth_prime_14 nth_prime_15 (by norm_num)
  · exact andrica_at_of_values nth_prime_15 nth_prime_16 (by norm_num)
  · exact andrica_at_of_values nth_prime_16 nth_prime_17 (by norm_num)
  · exact andrica_at_of_values nth_prime_17 nth_prime_18 (by norm_num)
  · exact andrica_at_of_values nth_prime_18 nth_prime_19 (by norm_num)
  · exact andrica_at_of_values nth_prime_19 nth_prime_20 (by norm_num)
  · exact andrica_at_of_values nth_prime_20 nth_prime_21 (by norm_num)
  · exact andrica_at_of_values nth_prime_21 nth_prime_22 (by norm_num)
  · exact andrica_at_of_values nth_prime_22 nth_prime_23 (by norm_num)
  · exact andrica_at_of_values nth_prime_23 nth_prime_24 (by norm_num)
  · exact andrica_at_of_values nth_prime_24 nth_prime_25 (by norm_num)

end Brockian.AndricaConjecture

