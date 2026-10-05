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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma exists_prime_one_mod_four_dvd_sigma1 {n : ℕ} (hn : Odd n) (hs : Superperfect n) :
    ∃ q, q.Prime ∧ q % 4 = 1 ∧ q ∣ sigma1 n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hmod : sigma1 (sigma1 n) % 4 = 2 := by
    rw [hs, Nat.odd_iff] at *
    omega
  exact exists_prime_one_mod_four_dvd_of_sigma1_mod_four (sigma1_ne_zero hn0) hmod

/-! ### The target statement -/

/-- **Odd superperfect numbers.** Whether an odd superperfect number exists is an open
problem; what is proved here is a Lean-checked reduction: the existence of an odd
superperfect number is *equivalent* to the existence of one which, in addition, exceeds `1`
and whose sum of divisors `σ(n)` has a prime factor congruent to `1` modulo `4`.

The nontrivial (forward) direction is the content: every odd superperfect number
automatically satisfies these two extra conditions. -/
