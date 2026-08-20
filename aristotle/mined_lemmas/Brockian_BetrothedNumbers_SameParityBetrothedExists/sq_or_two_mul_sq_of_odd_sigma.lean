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

theorem sq_or_two_mul_sq_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (hs : σ 1 n % 2 = 1) :
    ∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2 := by
  set e := n.factorization 2 with he
  set u := ordCompl[2] n with hu
  have hun : 2 ^ e * u = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hnd : ¬(2 ∣ u) := Nat.not_dvd_ordCompl Nat.prime_two hn
  have hu2 : u % 2 = 1 := by omega
  have hcop : Nat.Coprime (2 ^ e) u := (Nat.coprime_ordCompl Nat.prime_two hn).pow_left _
  have hmul : σ 1 (2 ^ e * u) = σ 1 (2 ^ e) * σ 1 u :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hun] at hmul
  rw [hmul, Nat.mul_mod] at hs
  have hsu : σ 1 u % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (σ 1 u) with h | h
    · rw [h] at hs; simp at hs
    · exact h
  obtain ⟨t, ht⟩ := isSquare_of_odd_of_odd_sigma u hu2 hsu
  rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨2 ^ j * t, Or.inl (by rw [← hun, ht, hj]; ring)⟩
  · exact ⟨2 ^ j * t, Or.inr (by rw [← hun, ht, hj]; ring)⟩

/-! ### Consequences for same-parity betrothed pairs -/

/-- In a same-parity betrothed pair both sums of divisors are odd (they equal the odd number
`m + n + 1`). -/
