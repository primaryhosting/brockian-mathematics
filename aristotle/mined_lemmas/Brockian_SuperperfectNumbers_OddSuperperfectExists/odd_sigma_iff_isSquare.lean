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

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`. Whether an odd superperfect
number exists is an open problem, so the target result
`Brockian.SuperperfectNumbers.OddSuperperfectExists` is a Lean-checked *conditional
reduction*: the existence of an odd superperfect number is equivalent to the existence of
one satisfying a list of proved necessary conditions (size lower bound from a kernel
computation, deficiency bounds, non-divisibility by `3` in the non-square case, and parity
information in the square case).
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

theorem odd_sigma_iff_isSquare {n : ℕ} (hpos : 0 < n) (hodd : Odd n) :
    Odd (sigma n) ↔ IsSquare n := by
  have hn : n ≠ 0 := hpos.ne'
  have hpar : sigma n % 2 = n.divisors.card % 2 := by
    refine sum_mod_two_eq_card_mod_two fun d hd => ?_
    exact Odd.of_dvd_nat hodd (Nat.mem_divisors.mp hd).1
  rw [← odd_card_divisors_iff_isSquare hn, Nat.odd_iff, Nat.odd_iff, hpar]

/-- **Kanold-type partial result.** An odd superperfect number divisible by `3`
must be a perfect square. -/
