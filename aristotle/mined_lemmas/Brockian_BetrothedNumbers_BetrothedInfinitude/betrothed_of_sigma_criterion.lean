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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` form a *betrothed* (or *quasi-amicable*) pair when the sum of
the divisors of each, excluding `1` and the number itself, equals the other number; equivalently
`σ m = σ n = m + n + 1`. -/

theorem betrothed_of_sigma_criterion {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : σ 1 ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1)) :
    IsBetrothedPair ((2 ^ k - 1) * (p + 2)) (2 ^ k * p) := by
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hppos : 0 < p := hp.pos
  have key := sigma_criterion_key k p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (by omega) (by omega)
  · exact Nat.mul_pos (by omega) hppos
  · -- the two numbers have different parities
    have hodd : Odd ((2 ^ k - 1) * (p + 2)) := by
      refine Odd.mul ?_ ?_
      · exact Nat.Even.sub_odd h1 ((Nat.even_pow' (by omega)).2 even_two) odd_one
      · exact (hp.odd_of_ne_two hp2).add_even (by decide)
    have heven : Even (2 ^ k * p) :=
      Even.mul_right ((Nat.even_pow' (by omega)).2 even_two) p
    intro hEq
    rw [hEq] at hodd
    exact (Nat.not_odd_iff_even.2 heven) hodd
  · rw [h, key]
  · rw [sigma_one_two_pow_mul_prime hp hp2, key]

/-- Conversely, a number of the shape `2 ^ k * p` (`k ≥ 1`, `p` an odd prime) has at most one
possible betrothed partner, namely `(2 ^ k - 1) * (p + 2)`. -/
