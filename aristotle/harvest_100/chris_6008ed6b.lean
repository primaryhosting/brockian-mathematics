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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! ... -/` module docstring,
-- since Lean 4 requires `import` commands to precede every other command, docstrings included.)

import Mathlib

open scoped Nat

namespace Brockian.TwinPrimes

/-- The **Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime.

This statement is a famous open problem, so it is recorded here as a `Prop`-valued
definition; the theorems below give Lean-checked equivalent reformulations of it. -/
def TwinPrimeConjecture : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- `ClementCondition n` is the arithmetic condition appearing in Clement's criterion:
`n * (n + 2)` divides `4 * ((n-1)! + 1) + n`. -/
def ClementCondition (n : ℕ) : Prop :=
  n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n

/-! ### Auxiliary lemmas -/

/-- An odd natural number is coprime to `4`. -/
theorem coprime_four_of_odd {n : ℕ} (hodd : Odd n) : Nat.Coprime n 4 := by
  have h2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hodd
  have h4 := h2.pow_right 2
  norm_num at h4
  exact h4

/-- An odd natural number is coprime to its shift by `2`. -/
theorem coprime_add_two_of_odd {n : ℕ} (hodd : Odd n) : Nat.Coprime n (n + 2) := by
  have h2 : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hodd
  simpa [Nat.Coprime, Nat.add_comm, Nat.gcd_comm, Nat.gcd_add_self_right] using h2

/-- Wilson's theorem in divisibility form: for `n ≥ 2`, `n` divides `(n-1)! + 1`
if and only if `n` is prime. -/
theorem dvd_factorial_pred_add_one_iff_prime {n : ℕ} (hn : 2 ≤ n) :
    n ∣ (n - 1)! + 1 ↔ Nat.Prime n := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega : n ≠ 1)]
  constructor
  · intro h; linear_combination (norm := ring_nf) h
  · intro h; rw [h]; ring

/-- The "left half" of Clement's criterion: for odd `n ≥ 3`, `n` divides
`4 * ((n-1)! + 1) + n` if and only if `n` is prime. -/
theorem dvd_iff_prime_left {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    n ∣ 4 * ((n - 1)! + 1) + n ↔ Nat.Prime n := by
  have h4 : Nat.Coprime n 4 := coprime_four_of_odd hodd
  rw [Nat.dvd_add_self_right]
  rw [show (4 : ℕ) * ((n - 1)! + 1) = ((n - 1)! + 1) * 4 by ring]
  constructor
  · intro h
    exact (dvd_factorial_pred_add_one_iff_prime (by omega)).mp (h4.dvd_of_dvd_mul_right h)
  · intro h
    exact Dvd.dvd.mul_right ((dvd_factorial_pred_add_one_iff_prime (by omega)).mpr h) 4

/-- A Wilson-type criterion for `n + 2`: for `n ≥ 3`, `n + 2` divides `2 * (n-1)! + 1`
if and only if `n + 2` is prime. -/
theorem dvd_two_mul_factorial_add_one_iff_prime {n : ℕ} (hn : 3 ≤ n) :
    (n + 2) ∣ 2 * (n - 1)! + 1 ↔ Nat.Prime (n + 2) := by
  have hfac : (n + 1)! = (n + 1) * n * (n - 1)! := by
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (by omega : n ≠ 0), mul_assoc]
  have hz : ((n : ℕ) : ZMod (n + 2)) = -2 := by
    have h0 : ((n + 2 : ℕ) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination h0
  rw [← ZMod.natCast_eq_zero_iff, Nat.prime_iff_fac_equiv_neg_one (by omega : n + 2 ≠ 1)]
  rw [show n + 2 - 1 = n + 1 by omega, hfac]
  push_cast [hz]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- The "right half" of Clement's criterion: for odd `n ≥ 3`, `n + 2` divides
`4 * ((n-1)! + 1) + n` if and only if `n + 2` is prime. -/
theorem dvd_iff_prime_right {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    (n + 2) ∣ 4 * ((n - 1)! + 1) + n ↔ Nat.Prime (n + 2) := by
  have hodd2 : Odd (n + 2) := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have h2 : Nat.Coprime (n + 2) 2 := Nat.coprime_two_right.mpr hodd2
  rw [show 4 * ((n - 1)! + 1) + n = (2 * (n - 1)! + 1) * 2 + (n + 2) by ring,
    Nat.dvd_add_self_right]
  constructor
  · intro h
    exact (dvd_two_mul_factorial_add_one_iff_prime hn).mp (h2.dvd_of_dvd_mul_right h)
  · intro h
    exact Dvd.dvd.mul_right ((dvd_two_mul_factorial_add_one_iff_prime hn).mpr h) 2

/-! ### Clement's criterion and reformulations of the conjecture -/

/-- **Clement's criterion** for twin primes: for odd `n ≥ 3`, the pair `(n, n+2)` is a twin
prime pair if and only if `n * (n + 2)` divides `4 * ((n-1)! + 1) + n`. -/
theorem clement_criterion {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    (Nat.Prime n ∧ Nat.Prime (n + 2)) ↔ ClementCondition n := by
  have hcop : Nat.Coprime n (n + 2) := coprime_add_two_of_odd hodd
  unfold ClementCondition
  constructor
  · rintro ⟨h1, h2⟩
    exact hcop.mul_dvd_of_dvd_of_dvd ((dvd_iff_prime_left hn hodd).mpr h1)
      ((dvd_iff_prime_right hn hodd).mpr h2)
  · intro h
    exact ⟨(dvd_iff_prime_left hn hodd).mp ((dvd_mul_right n (n + 2)).trans h),
      (dvd_iff_prime_right hn hodd).mp ((dvd_mul_left (n + 2) n).trans h)⟩

/-- Reformulation of the Twin Prime Conjecture as a purely elementary factorial-divisibility
statement (via Clement's criterion). -/
theorem twinPrimeConjecture_iff_clement :
    TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Odd n ∧ ClementCondition n := by
  constructor
  · intro h N
    obtain ⟨p, hp, hp1, hp2⟩ := h (max N 3)
    have hp3 : 3 ≤ p := le_trans (le_max_right N 3) hp
    have hodd : Odd p := hp1.odd_of_ne_two (by omega)
    exact ⟨p, le_trans (le_max_left N 3) hp, hodd, (clement_criterion hp3 hodd).mp ⟨hp1, hp2⟩⟩
  · intro h N
    obtain ⟨n, hn, hodd, hC⟩ := h (max N 3)
    have hn3 : 3 ≤ n := le_trans (le_max_right N 3) hn
    obtain ⟨h1, h2⟩ := (clement_criterion hn3 hodd).mpr hC
    exact ⟨n, le_trans (le_max_left N 3) hn, h1, h2⟩

/-- Contrapositive form: the Twin Prime Conjecture fails iff there is a bound `N` beyond which
no odd number satisfies Clement's condition. -/
theorem not_twinPrimeConjecture_iff :
    ¬ TwinPrimeConjecture ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ¬ ClementCondition n := by
  rw [twinPrimeConjecture_iff_clement]
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn hodd hC => (hN n hn hodd).elim hC⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn hodd => fun hC => absurd hC (hN n hn hodd)⟩

/-- The Twin Prime Conjecture is equivalent to the infinitude of the set of twin primes. -/
theorem twinPrimeConjecture_iff_infinite :
    TwinPrimeConjecture ↔ {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨b, hb⟩
    obtain ⟨p, hp, hp1, hp2⟩ := h (b + 1)
    exact absurd (hb (show p ∈ _ from ⟨hp1, hp2⟩)) (by omega)
  · intro h N
    obtain ⟨p, hpS, hp⟩ := h.exists_gt N
    exact ⟨p, le_of_lt hp, hpS.1, hpS.2⟩

end Brockian.TwinPrimes

