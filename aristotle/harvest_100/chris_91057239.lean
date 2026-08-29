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

import Mathlib

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/
def IsTwinPrime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (p + 2)

/-- The set of twin primes. -/
def twinPrimes : Set ℕ := {p | IsTwinPrime p}

theorem isTwinPrime_three : IsTwinPrime 3 := ⟨by norm_num, by norm_num⟩

theorem isTwinPrime_five : IsTwinPrime 5 := ⟨by norm_num, by norm_num⟩

theorem isTwinPrime_eleven : IsTwinPrime 11 := ⟨by norm_num, by norm_num⟩

/-- The twin prime conjecture (infinitude of twin primes) is equivalent to the unboundedness of
the set of twin primes. -/
theorem twinPrimes_infinite_iff :
    twinPrimes.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsTwinPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    obtain ⟨p, hlt, hp⟩ := h a
    exact ⟨p, hp, hlt⟩

/-! ### Clement's criterion

Clement's theorem: for `n ≥ 3`, the pair `(n, n + 2)` is a twin prime pair if and only if
`n * (n + 2)` divides `4 * ((n - 1)! + 1) + n`.  We prove this unconditionally; it converts the
twin prime conjecture into a purely arithmetic divisibility statement.
-/

/-- Auxiliary factorial identity: `(k + 4)! = (k + 4) * ((k + 3) * (k + 2)!)`. -/
private lemma factorial_step (k : ℕ) :
    (k + 4)! = (k + 4) * ((k + 3) * (k + 2)!) := by
  rw [show k + 4 = (k + 3) + 1 from rfl, Nat.factorial_succ,
    show k + 3 = (k + 2) + 1 from rfl, Nat.factorial_succ]

private lemma coprime_odd_two (j : ℕ) : Nat.Coprime (2 * j + 3) 2 := by
  simp [Nat.Coprime, Nat.gcd_comm]

private lemma coprime_odd_four (j : ℕ) : Nat.Coprime (2 * j + 3) 4 := by
  simpa using (coprime_odd_two j).pow_right 2

private lemma coprime_shift_two (j : ℕ) : Nat.Coprime (2 * j + 3) (2 * j + 5) := by
  have h1 := Nat.gcd_dvd_left (2 * j + 3) (2 * j + 5)
  have h2 := Nat.gcd_dvd_right (2 * j + 3) (2 * j + 5)
  have hd : Nat.gcd (2 * j + 3) (2 * j + 5) ∣ 2 :=
    (Nat.dvd_add_iff_right h1).mpr (by simp [show 2 * j + 5 = (2 * j + 3) + 2 from rfl] at h2 ⊢)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact h
  · rw [h] at h1; omega

/-- If `k + 5` is prime then, modulo `k + 5`, one has `2 * (k + 2)! = -1`. -/
private lemma two_factorial_eq (k : ℕ) (hq : Nat.Prime (k + 5)) :
    (2 : ZMod (k + 5)) * ((k + 2)! : ℕ) = -1 := by
  have hw := (Nat.prime_iff_fac_equiv_neg_one (n := k + 5) (by omega)).mp hq
  rw [show (k + 5) - 1 = k + 4 from rfl] at hw
  rw [factorial_step k] at hw
  have h0 : ((k : ZMod (k + 5)) + 5) = 0 := by
    have : ((k + 5 : ℕ) : ZMod (k + 5)) = 0 := ZMod.natCast_self _
    push_cast at this
    linear_combination this
  have hk4 : ((k : ZMod (k + 5)) + 4) = -1 := by linear_combination h0
  have hk3 : ((k : ZMod (k + 5)) + 3) = -2 := by linear_combination h0
  push_cast at hw
  rw [hk4, hk3] at hw
  linear_combination hw

/-- **Clement's criterion** (forward direction): if `n` and `n + 2` are both prime and `n ≥ 3`,
then `n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`. -/
theorem clement_of_isTwinPrime {n : ℕ} (hn : 3 ≤ n) (h : IsTwinPrime n) :
    n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨hp, hq⟩ := h
  have hq' : Nat.Prime (k + 5) := by simpa [show k + 3 + 2 = k + 5 from rfl] using hq
  rw [show (k + 3) - 1 = k + 2 from rfl]
  -- oddness of `k + 3`
  have hodd : ¬ (2 ∣ (k + 3)) := by
    intro h2
    have : (2 : ℕ) ∣ k + 5 := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hq' 2 this)
    omega
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  subst hj
  -- divisibility by `k + 3`
  have hdvd1 : (2 * j + 3) ∣ 4 * ((2 * j + 2)! + 1) + (2 * j + 3) := by
    have hw := (Nat.prime_iff_fac_equiv_neg_one (n := 2 * j + 3) (by omega)).mp hp
    rw [show (2 * j + 3) - 1 = 2 * j + 2 from rfl] at hw
    have hz : (((2 * j + 2)! + 1 : ℕ) : ZMod (2 * j + 3)) = 0 := by push_cast [hw]; ring
    have : (2 * j + 3) ∣ ((2 * j + 2)! + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact Dvd.dvd.add (this.mul_left 4) dvd_rfl
  -- divisibility by `k + 5`
  have hdvd2 : (2 * j + 5) ∣ 4 * ((2 * j + 2)! + 1) + (2 * j + 3) := by
    have h2 := two_factorial_eq (2 * j) hq'
    have hz : ((4 * ((2 * j + 2)! + 1) + (2 * j + 3) : ℕ) : ZMod (2 * j + 5)) = 0 := by
      have h0 : ((2 * j + 5 : ℕ) : ZMod (2 * j + 5)) = 0 := ZMod.natCast_self _
      push_cast at h2 h0 ⊢
      linear_combination 2 * h2 + h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_shift_two j) hdvd1 hdvd2
  simpa [show 2 * j + 3 + 2 = 2 * j + 5 from rfl] using this

/-- From Clement's divisibility one gets `(k + 5) ∣ 2 * (2 * (k + 2)! + 1)`. -/
private lemma dvd_two_mul_of_clement {k : ℕ}
    (h : (k + 3) * (k + 5) ∣ 4 * ((k + 2)! + 1) + (k + 3)) :
    (k + 5) ∣ 2 * (2 * (k + 2)! + 1) := by
  have hB : (k + 5) ∣ 4 * ((k + 2)! + 1) + (k + 3) := dvd_trans ⟨k + 3, by ring⟩ h
  have hz : ((4 * ((k + 2)! + 1) + (k + 3) : ℕ) : ZMod (k + 5)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hB
  have h0 : ((k + 5 : ℕ) : ZMod (k + 5)) = 0 := ZMod.natCast_self _
  refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
  push_cast at hz h0 ⊢
  linear_combination hz - h0

/-- From Clement's divisibility one gets `(k + 3) ∣ 4 * ((k + 2)! + 1)`. -/
private lemma dvd_four_mul_of_clement {k : ℕ}
    (h : (k + 3) * (k + 5) ∣ 4 * ((k + 2)! + 1) + (k + 3)) :
    (k + 3) ∣ 4 * ((k + 2)! + 1) := by
  have hA : (k + 3) ∣ 4 * ((k + 2)! + 1) + (k + 3) := dvd_trans ⟨k + 5, rfl⟩ h
  exact (Nat.dvd_add_iff_left dvd_rfl).mpr hA

/-- Clement's congruence for `n = k + 3` forces `n` to be odd, i.e. `k` to be even. -/
private lemma even_of_clement {k : ℕ}
    (h : (k + 3) * (k + 5) ∣ 4 * ((k + 2)! + 1) + (k + 3)) : ∃ j, k = 2 * j := by
  refine ⟨k / 2, ?_⟩
  by_contra hodd
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  have hB := dvd_two_mul_of_clement h
  have hB' : (j + 3) ∣ 2 * (2 * j + 1 + 2)! + 1 := by
    have : (2 : ℕ) * (j + 3) ∣ 2 * (2 * (2 * j + 1 + 2)! + 1) := by
      simpa [show 2 * j + 1 + 5 = 2 * (j + 3) by ring] using hB
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp this
  have hfac : (j + 3) ∣ (2 * j + 1 + 2)! :=
    Nat.dvd_factorial (by omega) (by omega)
  have : (j + 3) ∣ 1 := (Nat.dvd_add_iff_right (hfac.mul_left 2)).mpr hB'
  have := Nat.le_of_dvd one_pos this
  omega

/-- **Clement's criterion** (backward direction): if `n ≥ 3` and
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`, then `n` and `n + 2` are both prime. -/
theorem isTwinPrime_of_clement {n : ℕ} (hn : 3 ≤ n)
    (h : n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) : IsTwinPrime n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show (k + 3) - 1 = k + 2 from rfl, show k + 3 + 2 = k + 5 from rfl] at h
  obtain ⟨j, rfl⟩ := even_of_clement h
  constructor
  · -- `2 * j + 3` is prime, by Wilson's theorem
    have hA := dvd_four_mul_of_clement h
    have hA' : (2 * j + 3) ∣ ((2 * j + 2)! + 1) :=
      (coprime_odd_four j).dvd_of_dvd_mul_left hA
    have hz : (((2 * j + 2)! + 1 : ℕ) : ZMod (2 * j + 3)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hA'
    refine (Nat.prime_iff_fac_equiv_neg_one (n := 2 * j + 3) (by omega)).mpr ?_
    rw [show (2 * j + 3) - 1 = 2 * j + 2 from rfl]
    push_cast at hz
    linear_combination hz
  · -- `2 * j + 5` is prime, by Wilson's theorem
    have hB := dvd_two_mul_of_clement h
    have hcop : Nat.Coprime (2 * j + 5) 2 := by simp [Nat.Coprime, Nat.gcd_comm]
    have hB' : (2 * j + 5) ∣ (2 * (2 * j + 2)! + 1) := hcop.dvd_of_dvd_mul_left hB
    have hz : ((2 * (2 * j + 2)! + 1 : ℕ) : ZMod (2 * j + 5)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hB'
    have h0 : ((2 * j + 5 : ℕ) : ZMod (2 * j + 5)) = 0 := ZMod.natCast_self _
    have hk4 : ((2 * j : ZMod (2 * j + 5)) + 4) = -1 := by push_cast at h0 ⊢; linear_combination h0
    have hk3 : ((2 * j : ZMod (2 * j + 5)) + 3) = -2 := by push_cast at h0 ⊢; linear_combination h0
    refine (Nat.prime_iff_fac_equiv_neg_one (n := 2 * j + 3 + 2) (by omega)).mpr ?_
    rw [show (2 * j + 3 + 2) - 1 = 2 * j + 4 from rfl,
      show 2 * j + 4 = (2 * j) + 4 from rfl, factorial_step (2 * j)]
    push_cast at hz ⊢
    rw [show ((2 : ZMod (2 * j + 3 + 2)) * j + 4) = -1 from hk4,
      show ((2 : ZMod (2 * j + 3 + 2)) * j + 3) = -2 from hk3]
    linear_combination hz

/-- **Clement's criterion**. -/
theorem clement_iff {n : ℕ} (hn : 3 ≤ n) :
    IsTwinPrime n ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n :=
  ⟨clement_of_isTwinPrime hn, isTwinPrime_of_clement hn⟩

/-- A concrete instance of Clement's congruence: `5 * 7 ∣ 4 * (4! + 1) + 5 = 105`. -/
example : (5 : ℕ) * (5 + 2) ∣ 4 * ((5 - 1)! + 1) + 5 := by decide

/-- Every twin prime is at least `3`. -/
theorem three_le_of_isTwinPrime {p : ℕ} (h : IsTwinPrime p) : 3 ≤ p := by
  have h2 := h.1.two_le
  rcases Nat.lt_or_ge p 3 with hlt | hge
  · interval_cases p
    · exact absurd h.2 (by norm_num)
  · exact hge

/-- The set of twin primes is exactly the set of solutions `n ≥ 3` of Clement's congruence. -/
theorem twinPrimes_eq_clement_solutions :
    twinPrimes = {n : ℕ | 3 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n} := by
  ext n
  constructor
  · intro hn
    have h3 := three_le_of_isTwinPrime hn
    exact ⟨h3, clement_of_isTwinPrime h3 hn⟩
  · rintro ⟨h3, hd⟩
    exact isTwinPrime_of_clement h3 hd

/-- **Reduction of the twin prime conjecture to an elementary divisibility statement.**
There are infinitely many twin primes if and only if Clement's congruence
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n` has arbitrarily large solutions `n ≥ 3`. -/
theorem twinPrimes_infinite_iff_clement :
    twinPrimes.Infinite ↔
      ∀ N : ℕ, ∃ n, N < n ∧ 3 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  rw [twinPrimes_infinite_iff]
  constructor
  · intro h N
    obtain ⟨p, hlt, hp⟩ := h N
    have h3 := three_le_of_isTwinPrime hp
    exact ⟨p, hlt, h3, clement_of_isTwinPrime h3 hp⟩
  · intro h N
    obtain ⟨n, hlt, h3, hd⟩ := h N
    exact ⟨n, hlt, isTwinPrime_of_clement h3 hd⟩

/-- **Conditional reduction of the twin prime conjecture.**  If for every bound `N` there is some
`n > N` with `n ≥ 3` satisfying Clement's divisibility congruence
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`, then there are infinitely many twin primes. -/
theorem TwinPrimeConjecture
    (h : ∀ N : ℕ, ∃ n, N < n ∧ 3 ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) :
    twinPrimes.Infinite :=
  twinPrimes_infinite_iff_clement.mpr h

end Brockian.TwinPrimes

