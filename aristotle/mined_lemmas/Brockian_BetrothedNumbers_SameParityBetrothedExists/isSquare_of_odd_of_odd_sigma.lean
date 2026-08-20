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

theorem isSquare_of_odd_of_odd_sigma (n : ℕ) (hn : n % 2 = 1) (hs : σ 1 n % 2 = 1) :
    IsSquare n := by
  induction n using Nat.recOnPrimePow with
  | zero => simp at hn
  | one => exact ⟨1, rfl⟩
  | prime_pow_mul a p k hp hpa hk ih =>
    have hp2 : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with rfl | h
      · exact absurd hn (by
          have : 2 ∣ 2 ^ k * a := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) a
          omega)
      · exact h
    have ha2 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h | h
      · have h2 : (2 : ℕ) ∣ a := by omega
        have : (2 : ℕ) ∣ p ^ k * a := h2.mul_left _
        omega
      · exact h
    have hcop : Nat.Coprime (p ^ k) a := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).pow_left _
    have hmul : σ 1 (p ^ k * a) = σ 1 (p ^ k) * σ 1 a :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
    rw [hmul, Nat.mul_mod] at hs
    have hs2 : σ 1 a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (σ 1 a) with h | h
      · rw [h] at hs; simp at hs
      · exact h
    have hs1 : σ 1 (p ^ k) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (σ 1 (p ^ k)) with h | h
      · rw [h] at hs; simp at hs
      · exact h
    have hk2 : k % 2 = 0 := by
      have := sigma_prime_pow_mod_two k hp hp2
      omega
    obtain ⟨t, ht⟩ := ih ha2 hs2
    refine ⟨p ^ (k / 2) * t, ?_⟩
    have hpk : p ^ k = p ^ (k / 2) * p ^ (k / 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [ht, hpk]
    ring

/-- If `t` is odd then `σ (t ^ 2)` is odd. -/
