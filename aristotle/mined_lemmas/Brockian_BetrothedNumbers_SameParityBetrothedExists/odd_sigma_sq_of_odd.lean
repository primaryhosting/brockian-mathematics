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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Betrothed (quasi-amicable) numbers

Two distinct positive integers `m ≠ n` are *betrothed* (or *quasi-amicable*) when each is the
sum of the non-trivial proper divisors of the other, i.e.

  `σ m = σ n = m + n + 1`,

where `σ = σ₁` is the sum-of-divisors function.  Examples are `(48, 75)`, `(140, 195)`,
`(1050, 1925)`, ....  In every known example the two members have *opposite* parity, and whether a
betrothed pair of the *same* parity exists is an open problem.

This file states that open problem as `SameParityBetrothedExists` and proves everything about it
that we can:

* `betrothed_48_75` : betrothed pairs do exist (and this one has opposite parity);
* `odd_sigma_iff_isSquare_of_odd` : for odd `n`, `σ n` is odd iff `n` is a perfect square;
* `sq_or_two_mul_sq_of_odd_sigma` : if `σ n` is odd (`n ≠ 0`) then `n = k ^ 2` or `n = 2 * k ^ 2`;
* `sameParity_structure` : both members of a same-parity betrothed pair are of the form
  `k ^ 2` or `2 * k ^ 2`, and if they are odd they are perfect squares;
* `no_sameParity_betrothed_lt_500` : a kernel-checked verification that no same-parity betrothed
  pair has a member below `500`;
* `sameParityBetrothedExists_reduction` : the resulting conditional reduction of the open problem.
-/

namespace Brockian.BetrothedNumbers

open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` : `m` and `n` are distinct positive integers each of which is the sum of the
non-trivial proper divisors of the other, i.e. `σ m = σ n = m + n + 1`.  (Such pairs are also
called *quasi-amicable* or *reduced amicable* pairs.) -/

theorem odd_sigma_sq_of_odd (t : ℕ) (ht : t % 2 = 1) : σ 1 (t ^ 2) % 2 = 1 := by
  induction t using Nat.recOnPrimePow with
  | zero => simp at ht
  | one => simp
  | prime_pow_mul a p k hp hpa hk ih =>
    have hp2 : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with rfl | h
      · exact absurd ht (by
          have : 2 ∣ 2 ^ k * a := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) a
          omega)
      · exact h
    have ha2 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h | h
      · have h2 : (2 : ℕ) ∣ a := by omega
        have : (2 : ℕ) ∣ p ^ k * a := h2.mul_left _
        omega
      · exact h
    have hcop : Nat.Coprime (p ^ (2 * k)) (a ^ 2) :=
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).pow_left _).pow_right _
    have hrw : (p ^ k * a) ^ 2 = p ^ (2 * k) * a ^ 2 := by ring
    rw [hrw, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.mul_mod,
      sigma_prime_pow_mod_two (2 * k) hp hp2, ih ha2]
    omega

/-- For odd `n`, `σ n` is odd exactly when `n` is a perfect square. -/
