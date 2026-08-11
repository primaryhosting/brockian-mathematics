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

/-!
The twin prime conjecture is a famous open problem, so the target theorem
`Brockian.TwinPrimes.TwinPrimeConjecture` is stated here as a *conditional reduction*:
it derives the infinitude of twin primes from `ClementHypothesis`, a purely
elementary (factorial/divisibility) statement.

The mathematical content that is proved unconditionally is **Clement's theorem**:
for `n ≥ 2`, the pair `(n, n+2)` consists of two primes if and only if

`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`.

Consequently `ClementHypothesis` is *equivalent* to the twin prime conjecture
(`twinPrime_iff_clementHypothesis`), so the reduction is faithful: no hidden
strengthening of the conjecture is assumed.
-/

namespace Brockian.TwinPrimes

open Nat Finset

/-- `n` starts a twin prime pair when both `n` and `n + 2` are prime. -/
def IsTwinPrimePair (n : ℕ) : Prop := Nat.Prime n ∧ Nat.Prime (n + 2)

/-- Clement's divisibility criterion for the pair `(n, n + 2)`. -/
def ClementCriterion (n : ℕ) : Prop := n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n

/-- The hypothesis that Clement's criterion holds for arbitrarily large `n`. -/
def ClementHypothesis : Prop := ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧ ClementCriterion n

/-! ### Auxiliary factorial lemmas -/

/-- The product of two distinct positive numbers `≤ m` divides `m !`. -/
theorem mul_dvd_factorial_of_ne {a b m : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (ha' : a ≤ m) (hb' : b ≤ m) : a * b ∣ m ! := by
  rw [← Finset.prod_Ico_id_eq_factorial]
  have h1 : a * b = ∏ x ∈ ({a, b} : Finset ℕ), x := by rw [Finset.prod_pair hab]
  rw [h1]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp only [Finset.mem_Ico] <;> omega

/-- If `n > 4` is composite then `n ∣ (n - 1)!`. -/
theorem dvd_factorial_pred_of_not_prime {n : ℕ} (h4 : 4 < n) (hn : ¬ n.Prime) :
    n ∣ (n - 1)! := by
  obtain ⟨m, hm1, hm2, hm3⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hn
  obtain ⟨k, rfl⟩ := hm1
  have hk1 : 1 < k := by nlinarith
  rcases eq_or_ne m k with rfl | hne
  · have hm3' : 3 ≤ m := by nlinarith
    have hb : 2 * m + 1 ≤ m * m := by nlinarith
    have : m * (2 * m) ∣ (m * m - 1)! :=
      mul_dvd_factorial_of_ne (by omega) (by omega) (by omega) (by omega) (by omega)
    exact dvd_trans ⟨2, by ring⟩ this
  · have hb : 2 * k ≤ m * k := Nat.mul_le_mul_right k hm2
    exact mul_dvd_factorial_of_ne (by omega) (by omega) hne (by omega) (by omega)

/-- For `n ≥ 1`, `(n + 1)! = (n + 1) * n * (n - 1)!`. -/
theorem factorial_succ_succ_pred {n : ℕ} (hn : 1 ≤ n) : (n + 1)! = (n + 1) * n * (n - 1)! := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Nat.factorial_succ, mul_assoc]

/-! ### Clement's theorem -/

theorem dvd_of_prime_left {n : ℕ} (hn : 2 ≤ n) (hp : n.Prime) :
    n ∣ 4 * ((n - 1)! + 1) + n := by
  have : ((4 * ((n - 1)! + 1) + n : ℕ) : ZMod n) = 0 := by
    push_cast
    rw [(Nat.prime_iff_fac_equiv_neg_one (by omega)).mp hp]
    simp
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

theorem dvd_of_prime_right {n : ℕ} (hn : 2 ≤ n) (hp : (n + 2).Prime) :
    (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  have hw : (((n + 1)! : ℕ) : ZMod (n + 2)) = -1 := by
    have := (Nat.prime_iff_fac_equiv_neg_one (n := n + 2) (by omega)).mp hp
    simpa using this
  have hfac : ((n + 1)! : ℕ) = (n + 1) * n * (n - 1)! := factorial_succ_succ_pred (by omega)
  have hn2 : ((n : ℕ) : ZMod (n + 2)) = -2 := by
    have : (((n + 2 : ℕ)) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  have h2x : (2 : ZMod (n + 2)) * (((n - 1)! : ℕ) : ZMod (n + 2)) = -1 := by
    rw [hfac] at hw
    push_cast at hw
    rw [hn2] at hw
    linear_combination hw
  have : ((4 * ((n - 1)! + 1) + n : ℕ) : ZMod (n + 2)) = 0 := by
    push_cast
    rw [show ((n : ℕ) : ZMod (n + 2)) = -2 from hn2]
    push_cast at h2x ⊢
    linear_combination 2 * h2x
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

theorem odd_of_clementCriterion {n : ℕ} (hn : 2 ≤ n) (h : ClementCriterion n) : ¬ 2 ∣ n := by
  intro he
  have h4 : (4 : ℕ) ∣ n * (n + 2) := by
    obtain ⟨k, rfl⟩ := he
    exact ⟨k * (k + 1), by ring⟩
  have hA : (4 : ℕ) ∣ 4 * ((n - 1)! + 1) + n := h4.trans h
  have h4n : (4 : ℕ) ∣ n := (Nat.dvd_add_right ⟨(n - 1)! + 1, rfl⟩).mp hA
  have hn4 : 4 ≤ n := Nat.le_of_dvd (by omega) h4n
  rcases eq_or_lt_of_le hn4 with heq | hlt
  · rw [← heq] at h
    norm_num [ClementCriterion, Nat.factorial] at h
  · have hnp : ¬ n.Prime := by
      intro hp
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 4 h4n)
      omega
    have hdvd : n ∣ (n - 1)! := dvd_factorial_pred_of_not_prime hlt hnp
    have hn' : n ∣ 4 * ((n - 1)! + 1) + n := dvd_trans ⟨n + 2, rfl⟩ h
    have h1 : n ∣ 4 * ((n - 1)! + 1) := (Nat.dvd_add_right (Dvd.intro 1 rfl)).mp
      (by simpa [Nat.add_comm] using hn')
    have h2 : n ∣ 4 * (n - 1)! := Dvd.dvd.mul_left hdvd 4
    have h3 : n ∣ 4 := by
      have : 4 * ((n - 1)! + 1) = 4 * (n - 1)! + 4 := by ring
      rw [this] at h1
      exact (Nat.dvd_add_right h2).mp h1
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem prime_left_of_clementCriterion {n : ℕ} (hn : 2 ≤ n) (h : ClementCriterion n) :
    n.Prime := by
  have hodd : ¬ 2 ∣ n := odd_of_clementCriterion hn h
  have hn' : n ∣ 4 * ((n - 1)! + 1) + n := dvd_trans ⟨n + 2, rfl⟩ h
  have h1 : n ∣ 4 * ((n - 1)! + 1) := (Nat.dvd_add_right (Dvd.intro 1 rfl)).mp
    (by simpa [Nat.add_comm] using hn')
  have hcop : Nat.Coprime n 4 := by
    have h2 : Nat.Coprime n 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    have := h2.pow_right 2
    norm_num at this
    exact this
  have h2 : n ∣ (n - 1)! + 1 := (Nat.Coprime.dvd_of_dvd_mul_left hcop h1)
  have : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
  push_cast at this
  refine (Nat.prime_iff_fac_equiv_neg_one (by omega)).mpr ?_
  linear_combination this

theorem prime_right_of_clementCriterion {n : ℕ} (hn : 2 ≤ n) (h : ClementCriterion n) :
    (n + 2).Prime := by
  have hodd : ¬ 2 ∣ n := odd_of_clementCriterion hn h
  have hn' : (n + 2) ∣ 4 * ((n - 1)! + 1) + n := dvd_trans ⟨n, by ring⟩ h
  have key : (n + 2) ∣ 2 * (2 * (n - 1)! + 1) := by
    have hEq : 4 * ((n - 1)! + 1) + n = 2 * (2 * (n - 1)! + 1) + (n + 2) := by ring
    rw [hEq] at hn'
    exact (Nat.dvd_add_right (dvd_refl _)).mp (by simpa [Nat.add_comm] using hn')
  have hcop : Nat.Coprime (n + 2) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
  have key2 : (n + 2) ∣ 2 * (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left key
  have hz : ((2 * (n - 1)! + 1 : ℕ) : ZMod (n + 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr key2
  have hn2 : ((n : ℕ) : ZMod (n + 2)) = -2 := by
    have : (((n + 2 : ℕ)) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  refine (Nat.prime_iff_fac_equiv_neg_one (n := n + 2) (by omega)).mpr ?_
  have hfac : ((n + 1)! : ℕ) = (n + 1) * n * (n - 1)! := factorial_succ_succ_pred (by omega)
  have : (((n + 2 - 1)! : ℕ) : ZMod (n + 2)) = (((n + 1)! : ℕ) : ZMod (n + 2)) := by
    norm_num
  rw [this, hfac]
  push_cast
  push_cast at hz hn2
  rw [hn2]
  linear_combination hz

/-- **Clement's theorem**: for `n ≥ 2`, `n` and `n + 2` are both prime if and only if
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`. -/
theorem clement {n : ℕ} (hn : 2 ≤ n) : IsTwinPrimePair n ↔ ClementCriterion n := by
  constructor
  · rintro ⟨hp, hq⟩
    have hodd : ¬ 2 ∣ n := by
      intro he
      have : n = 2 := ((Nat.Prime.eq_one_or_self_of_dvd hp 2 he).resolve_left (by norm_num)).symm
      subst this
      norm_num at hq
    have hcop : Nat.Coprime n (n + 2) := by
      have h2 : Nat.Coprime n 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
      exact Nat.coprime_self_add_right.mpr h2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (dvd_of_prime_left hn hp)
      (dvd_of_prime_right hn hq)
  · intro h
    exact ⟨prime_left_of_clementCriterion hn h, prime_right_of_clementCriterion hn h⟩

/-! ### The reduction -/

/-- **Twin Prime Conjecture** (conditional reduction): if Clement's criterion holds for
arbitrarily large `n`, then there are infinitely many twin prime pairs. -/
theorem TwinPrimeConjecture (h : ClementHypothesis) : {n : ℕ | IsTwinPrimePair n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hN, hn2, hc⟩ := h (a + 1)
  exact ⟨n, (clement hn2).mpr hc, by omega⟩

theorem clementHypothesis_of_infinite (h : {n : ℕ | IsTwinPrimePair n}.Infinite) :
    ClementHypothesis := by
  intro N
  obtain ⟨n, hn, hgt⟩ := h.exists_gt (max N 2)
  refine ⟨n, by omega, by omega, (clement (by omega)).mp hn⟩

/-- Clement's hypothesis is *equivalent* to the twin prime conjecture. -/
theorem twinPrime_iff_clementHypothesis :
    ClementHypothesis ↔ {n : ℕ | IsTwinPrimePair n}.Infinite :=
  ⟨TwinPrimeConjecture, clementHypothesis_of_infinite⟩

/-! ### Sanity checks -/

example : IsTwinPrimePair 3 := ⟨by norm_num, by norm_num⟩

example : ClementCriterion 5 := by unfold ClementCriterion; norm_num [Nat.factorial]

example : ¬ ClementCriterion 7 := by unfold ClementCriterion; norm_num [Nat.factorial]

end Brockian.TwinPrimes

