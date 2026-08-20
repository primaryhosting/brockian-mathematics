/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)


/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat

namespace Brockian.TwinPrimes

/-! ## The statement

The twin prime conjecture asserts that there are arbitrarily large primes `p` such that
`p + 2` is also prime.  This is a famous open problem, so it is not proved here; instead
we give an unconditional, Lean-checked *equivalent reformulation* (Clement's criterion,
derived from Wilson's theorem — `Nat.prime_iff_fac_equiv_neg_one` in Mathlib), which
turns the conjecture into a single divisibility statement about factorials, together with
some unconditional partial results.
-/

/-- `n` and `n + 2` are both prime. -/
def IsTwinPrimePair (n : ℕ) : Prop := Nat.Prime n ∧ Nat.Prime (n + 2)

/-- **The Twin Prime Conjecture**: there are arbitrarily large twin prime pairs. -/
def TwinPrimeConjecture : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsTwinPrimePair p

/-- Equivalent phrasing of the conjecture: the set of twin primes is infinite. -/
theorem twinPrimeConjecture_iff_infinite :
    TwinPrimeConjecture ↔ {p : ℕ | IsTwinPrimePair p}.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hp, hpp⟩ := h N
    exact absurd (hN hpp) (by omega)
  · intro h N
    obtain ⟨p, hp, hpN⟩ := h.exists_gt N
    exact ⟨p, hpN, hp⟩

/-! ## Wilson's theorem, in divisibility form -/

/-- **Wilson's theorem** as a divisibility statement: for `n ≠ 1`, `n` is prime iff
`n ∣ (n-1)! + 1`. -/
theorem prime_iff_dvd_factorial_pred_succ (n : ℕ) (h : n ≠ 1) :
    Nat.Prime n ↔ n ∣ (n - 1)! + 1 := by
  rcases eq_or_ne n 0 with rfl | h0
  · simp [Nat.not_prime_zero]
  haveI : NeZero n := ⟨h0⟩
  rw [Nat.prime_iff_fac_equiv_neg_one h, ← ZMod.natCast_eq_zero_iff ((n - 1)! + 1) n]
  push_cast
  exact ⟨fun hh => by rw [hh]; ring, fun hh => by linear_combination hh⟩

/-! ## Clement's criterion -/

/-- Reduction of the divisibility condition modulo `2k+1`. -/
theorem dvd_left_iff (k : ℕ) :
    (2 * k + 1) ∣ 4 * ((2 * k)! + 1) + (2 * k + 1) ↔ (2 * k + 1) ∣ (2 * k)! + 1 := by
  rw [show 4 * ((2 * k)! + 1) + (2 * k + 1) = (2 * k + 1) + 4 * ((2 * k)! + 1) from by ring,
    Nat.dvd_add_right (dvd_refl _)]
  have h2 : Nat.Coprime (2 * k + 1) 2 := (Nat.coprime_mul_left_add_left 1 2 k).mpr rfl
  have hcop : Nat.Coprime (2 * k + 1) 4 := by
    simpa [show (4 : ℕ) = 2 * 2 by norm_num] using h2.mul_right h2
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => h.mul_left 4⟩

/-- Reduction of the divisibility condition modulo `2k+3`. -/
theorem dvd_right_iff (k : ℕ) :
    (2 * k + 3) ∣ 4 * ((2 * k)! + 1) + (2 * k + 1) ↔ (2 * k + 3) ∣ (2 * k + 2)! + 1 := by
  have hfac : (2 * k + 2)! + 1 = (2 * k + 3) * (2 * k * (2 * k)!) + (2 * (2 * k)! + 1) := by
    have h1 : (2 * k + 2)! = (2 * k + 2) * ((2 * k + 1) * (2 * k)!) := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [h1]; ring
  have hX : 4 * ((2 * k)! + 1) + (2 * k + 1) = (2 * k + 3) + 2 * (2 * (2 * k)! + 1) := by ring
  rw [hfac, hX, Nat.dvd_add_right (dvd_refl _), Nat.dvd_add_right (Dvd.intro _ rfl)]
  have hcop : Nat.Coprime (2 * k + 3) 2 := (Nat.coprime_mul_left_add_left 3 2 k).mpr rfl
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => h.mul_left 2⟩

/-- Consecutive odd numbers are coprime. -/
theorem coprime_two_mul_add_one_add_three (k : ℕ) : Nat.Coprime (2 * k + 1) (2 * k + 3) := by
  have h2 : Nat.gcd (2 * k + 1) (2 * k + 3) ∣ 2 := by
    have := Nat.dvd_sub (Nat.gcd_dvd_right (2 * k + 1) (2 * k + 3))
      (Nat.gcd_dvd_left (2 * k + 1) (2 * k + 3))
    simpa using this
  have h1 : Nat.gcd (2 * k + 1) (2 * k + 3) ∣ (2 * k + 1) := Nat.gcd_dvd_left _ _
  have hle := Nat.le_of_dvd (by norm_num) h2
  interval_cases h : Nat.gcd (2 * k + 1) (2 * k + 3) <;> omega

/-- **Clement's criterion** (1949): for `k ≥ 1`, the numbers `2k+1` and `2k+3` form a twin
prime pair if and only if `(2k+1)(2k+3) ∣ 4((2k)! + 1) + (2k+1)`. -/
theorem clement (k : ℕ) (hk : 1 ≤ k) :
    IsTwinPrimePair (2 * k + 1) ↔
      (2 * k + 1) * (2 * k + 3) ∣ 4 * ((2 * k)! + 1) + (2 * k + 1) := by
  have hw1 : Nat.Prime (2 * k + 1) ↔ (2 * k + 1) ∣ (2 * k)! + 1 := by
    have := prime_iff_dvd_factorial_pred_succ (2 * k + 1) (by omega)
    simpa using this
  have hw2 : Nat.Prime (2 * k + 3) ↔ (2 * k + 3) ∣ (2 * k + 2)! + 1 := by
    have := prime_iff_dvd_factorial_pred_succ (2 * k + 3) (by omega)
    simpa [show 2 * k + 3 - 1 = 2 * k + 2 from by omega] using this
  have hpair : IsTwinPrimePair (2 * k + 1) ↔ Nat.Prime (2 * k + 1) ∧ Nat.Prime (2 * k + 3) := by
    rw [IsTwinPrimePair, show 2 * k + 1 + 2 = 2 * k + 3 from by ring]
  rw [hpair, hw1, hw2, ← dvd_left_iff k, ← dvd_right_iff k]
  constructor
  · exact fun ⟨ha, hb⟩ => (coprime_two_mul_add_one_add_three k).mul_dvd_of_dvd_of_dvd ha hb
  · exact fun h => ⟨dvd_trans (Dvd.intro _ rfl) h, dvd_trans (Dvd.intro_left _ rfl) h⟩

/-- **A Lean-checked reduction of the Twin Prime Conjecture to a factorial divisibility
statement.**  The conjecture holds if and only if for every `N` there is some `k > N` with
`(2k+1)(2k+3) ∣ 4((2k)! + 1) + (2k+1)`. -/
theorem twinPrimeConjecture_iff_clement :
    TwinPrimeConjecture ↔
      ∀ N : ℕ, ∃ k : ℕ, N < k ∧
        (2 * k + 1) * (2 * k + 3) ∣ 4 * ((2 * k)! + 1) + (2 * k + 1) := by
  constructor
  · intro h N
    obtain ⟨p, hp, hpp⟩ := h (2 * N + 3)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.1.odd_of_ne_two (by omega))
    obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
    refine ⟨k, by omega, ?_⟩
    rw [← clement k (by omega), ← hk]
    exact hpp
  · intro h N
    obtain ⟨k, hk, hdvd⟩ := h (N + 1)
    exact ⟨2 * k + 1, by omega, (clement k (by omega)).mpr hdvd⟩

/-! ## Unconditional partial results -/

/-- `(3, 5)` is a twin prime pair, so twin primes exist. -/
theorem exists_twinPrimePair : ∃ p : ℕ, IsTwinPrimePair p :=
  ⟨3, by norm_num [IsTwinPrimePair]⟩

/-- Clement's criterion at `k = 2` confirms the twin prime pair `(5, 7)`. -/
theorem clement_five_seven : (2 * 2 + 1) * (2 * 2 + 3) ∣ 4 * ((2 * 2)! + 1) + (2 * 2 + 1) := by
  decide

/-- Clement's criterion at `k = 3` rejects `(7, 9)`, since `9` is not prime. -/
theorem not_clement_seven_nine :
    ¬ ((2 * 3 + 1) * (2 * 3 + 3) ∣ 4 * ((2 * 3)! + 1) + (2 * 3 + 1)) := by
  decide

/-- Apart from `(3,5)`, every twin prime pair `(p, p+2)` satisfies `p ≡ 5 [MOD 6]`. -/
theorem twinPrimePair_mod_six {p : ℕ} (hp : IsTwinPrimePair p) (h3 : 3 < p) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : ¬ (2 ∣ p) := fun h => by
    have := hp1.eq_one_or_self_of_dvd 2 h; omega
  have h3' : ¬ (3 ∣ p) := fun h => by
    have := hp1.eq_one_or_self_of_dvd 3 h; omega
  have h3'' : ¬ (3 ∣ (p + 2)) := fun h => by
    have := hp2.eq_one_or_self_of_dvd 3 h; omega
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3' h3''
  have e2 : p % 6 % 2 = p % 2 := Nat.mod_mod_of_dvd p (by norm_num)
  have e3 : p % 6 % 3 = p % 3 := Nat.mod_mod_of_dvd p (by norm_num)
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p % 6 <;> omega

end Brockian.TwinPrimes

