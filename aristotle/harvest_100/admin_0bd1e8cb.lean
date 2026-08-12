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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Twin Prime Conjecture is a famous open problem; it is stated below as
`Brockian.TwinPrimes.TwinPrimeConjecture`.  What this file establishes, fully and
axiom-cleanly, is a set of Lean-checked *reductions* and *partial results*:

* `twinPrimeConjecture_iff_infinite` : the conjecture is equivalent to the infinitude of
  the set of twin primes;
* `clement` : **Clement's criterion** — for `n ≥ 2`, `n` and `n + 2` are both prime iff
  `n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`;
* `twinPrimeConjecture_iff_clement` : consequently the conjecture is equivalent to a purely
  arithmetic statement about factorial congruences;
* `not_twinPrimeConjecture_iff_bddAbove` : its negation is equivalent to the existence of a
  largest twin prime pair;
* unconditional partial results: `six_dvd_succ_of_twin` and `twin_primes_small`.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `p` is the smaller member of a twin prime pair. -/
def IsTwinPrimePair (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- **The Twin Prime Conjecture**: there are arbitrarily large twin prime pairs. -/
def TwinPrimeConjecture : Prop := ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ IsTwinPrimePair p

/-- The conjecture is equivalent to the infinitude of the set of twin primes. -/
theorem twinPrimeConjecture_iff_infinite :
    TwinPrimeConjecture ↔ {p : ℕ | IsTwinPrimePair p}.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hp, hpp⟩ := h (a + 1)
    exact ⟨p, hpp, by omega⟩
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt.le, hp⟩

/-- The conjecture fails exactly when there is a largest twin prime pair. -/
theorem not_twinPrimeConjecture_iff_bddAbove :
    ¬ TwinPrimeConjecture ↔ ∃ M : ℕ, ∀ p : ℕ, IsTwinPrimePair p → p ≤ M := by
  unfold TwinPrimeConjecture
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp => by by_contra h; exact absurd hp (hN p (by omega))⟩
  · rintro ⟨M, hM⟩
    exact ⟨M + 1, fun p hp hpp => by have := hM p hpp; omega⟩

/-! ## Clement's criterion -/

/-- Half of the forward direction of Clement's criterion: divisibility by `n`.
This is Wilson's theorem for `n`. -/
theorem dvd_of_prime_left {n : ℕ} (hp : n.Prime) : n ∣ 4 * ((n - 1)! + 1) + n := by
  have h1 : n ∣ (n - 1)! + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [(Nat.prime_iff_fac_equiv_neg_one hp.ne_one).1 hp]
    ring
  exact Dvd.dvd.add (Dvd.dvd.mul_left h1 4) dvd_rfl

/-- Half of the forward direction of Clement's criterion: divisibility by `n + 2`.
This is Wilson's theorem for `n + 2`, using `(n+1)! = (n+1) * n * (n-1)!`. -/
theorem dvd_of_prime_right {n : ℕ} (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hp' : (m + 3).Prime := by convert hp using 2
  have hw : (((m + 2)! : ℕ) : ZMod (m + 3)) = -1 := by
    have := (Nat.prime_iff_fac_equiv_neg_one hp'.ne_one).1 hp'
    simpa using this
  have hfac : (m + 2)! = (m + 2) * ((m + 1) * m !) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  rw [hfac] at hw
  push_cast at hw
  have hx : ((m : ℕ) : ZMod (m + 3)) = -3 := by
    have := ZMod.natCast_self (m + 3)
    push_cast at this
    linear_combination this
  rw [hx] at hw
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hx]
  linear_combination 2 * hw

/-- If `n * (n + 2)` divides `4 * ((n-1)! + 1) + n` with `2 ≤ n`, then `n` is odd. -/
theorem odd_of_dvd {n : ℕ} (hn : 2 ≤ n) (hd : n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) :
    ¬ (2 ∣ n) := by
  intro he
  have hnX : n ∣ 4 * ((n - 1)! + 1) := by
    have h1 : n ∣ 4 * ((n - 1)! + 1) + n := dvd_trans (Dvd.intro _ rfl) hd
    have := Nat.dvd_sub h1 (dvd_refl n)
    simpa using this
  by_cases hsmall : n = 2 ∨ n = 4 ∨ n = 8
  · rcases hsmall with rfl | rfl | rfl <;> norm_num [Nat.factorial] at hd
  · obtain ⟨d, hdn⟩ := he
    have hd3 : 3 ≤ d := by omega
    have hdfac : d ∣ (n - 1)! := Nat.dvd_factorial (by omega) (by omega)
    have hd4 : d ∣ 4 := by
      have h2 : d ∣ 4 * ((n - 1)! + 1) := dvd_trans ⟨2, by omega⟩ hnX
      have h3 : d ∣ 4 * (n - 1)! := Dvd.dvd.mul_left hdfac 4
      have h4 := Nat.dvd_sub h2 h3
      have h5 : 4 * ((n - 1)! + 1) - 4 * (n - 1)! = 4 := by omega
      rwa [h5] at h4
    have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
    interval_cases d
    · omega
    · omega

/-- Converse direction of Clement's criterion: the divisibility forces `n` to be prime. -/
theorem prime_left_of_dvd {n : ℕ} (hn : 2 ≤ n) (hd : n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) :
    n.Prime := by
  have hodd := odd_of_dvd hn hd
  have hcop : Nat.Coprime n 4 := by
    have h2 : Nat.Coprime n 2 := by
      rw [Nat.coprime_comm]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    simpa using h2.pow_right 2
  have hnX : n ∣ 4 * ((n - 1)! + 1) := by
    have h1 : n ∣ 4 * ((n - 1)! + 1) + n := dvd_trans (Dvd.intro _ rfl) hd
    have := Nat.dvd_sub h1 (dvd_refl n)
    simpa using this
  have hfac : n ∣ (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left hnX
  refine (Nat.prime_iff_fac_equiv_neg_one (by omega)).2 ?_
  have hz : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hfac
  push_cast at hz
  linear_combination hz

/-- Converse direction of Clement's criterion: the divisibility forces `n + 2` to be prime. -/
theorem prime_right_of_dvd {n : ℕ} (hn : 2 ≤ n) (hd : n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) :
    (n + 2).Prime := by
  have hodd := odd_of_dvd hn hd
  have hcop : Nat.Coprime (n + 2) 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have hp : (n + 2) ∣ 4 * ((n - 1)! + 1) + n := dvd_trans (Dvd.intro_left _ rfl) hd
  have h2 : (n + 2) ∣ 2 * (2 * (n - 1)! + 1) := by
    have h := Nat.dvd_sub hp (dvd_refl (n + 2))
    have he : 4 * ((n - 1)! + 1) + n - (n + 2) = 2 * (2 * (n - 1)! + 1) := by omega
    rwa [he] at h
  have h3 : (n + 2) ∣ 2 * (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h3
  have hp3 : (m + 3).Prime := by
    refine (Nat.prime_iff_fac_equiv_neg_one (by omega)).2 ?_
    have hz : ((2 * m ! + 1 : ℕ) : ZMod (m + 3)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (by convert h3 using 2)
    push_cast at hz
    have hx : ((m : ℕ) : ZMod (m + 3)) = -3 := by
      have := ZMod.natCast_self (m + 3)
      push_cast at this
      linear_combination this
    have hfac : (m + 3 - 1)! = (m + 2) * ((m + 1) * m !) := by
      show (m + 2)! = _
      rw [Nat.factorial_succ, Nat.factorial_succ]
    rw [hfac]
    push_cast
    rw [hx]
    linear_combination hz
  convert hp3 using 2

/-- **Clement's criterion** for twin primes: for `n ≥ 2`, the pair `(n, n + 2)` consists of
two primes if and only if `n * (n + 2)` divides `4 * ((n - 1)! + 1) + n`. -/
theorem clement {n : ℕ} (hn : 2 ≤ n) :
    IsTwinPrimePair n ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  constructor
  · rintro ⟨h1, h2⟩
    have hne : n ≠ 2 := by
      rintro rfl
      norm_num at h2
    have hodd : ¬ (2 ∣ n) := by
      intro hdvd
      rcases Nat.Prime.eq_one_or_self_of_dvd h1 2 hdvd with h | h <;> omega
    have hcop : Nat.Coprime n (n + 2) := by
      have h2' : Nat.Coprime n 2 := by
        rw [Nat.coprime_comm]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
      simpa [Nat.add_comm] using (Nat.coprime_add_self_right (m := n) (n := 2)).2 h2'
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (dvd_of_prime_left h1)
      (dvd_of_prime_right (by omega) h2)
  · intro hd
    exact ⟨prime_left_of_dvd hn hd, prime_right_of_dvd hn hd⟩

/-- A purely arithmetic (factorial congruence) reformulation of the Twin Prime Conjecture. -/
theorem twinPrimeConjecture_iff_clement :
    TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  constructor
  · intro h N
    obtain ⟨p, hp, hpp⟩ := h (max N 2)
    exact ⟨p, le_trans (le_max_left _ _) hp, (clement (le_trans (le_max_right _ _) hp)).1 hpp⟩
  · intro h N
    obtain ⟨n, hn, hdvd⟩ := h (max N 2)
    exact ⟨n, le_trans (le_max_left _ _) hn, (clement (le_trans (le_max_right _ _) hn)).2 hdvd⟩

/-! ## Unconditional partial results -/

/-- Every twin prime pair beyond `(3, 5)` is centred on a multiple of `6`. -/
theorem six_dvd_succ_of_twin {n : ℕ} (h : IsTwinPrimePair n) (h3 : 3 < n) : 6 ∣ n + 1 := by
  obtain ⟨hn, hn2⟩ := h
  have h2 : ¬ (2 ∣ n) := fun hd => by
    have := Nat.Prime.eq_one_or_self_of_dvd hn 2 hd; omega
  have h3' : ¬ (3 ∣ n) := fun hd => by
    have := Nat.Prime.eq_one_or_self_of_dvd hn 3 hd; omega
  have h3'' : ¬ (3 ∣ (n + 2)) := fun hd => by
    have := Nat.Prime.eq_one_or_self_of_dvd hn2 3 hd; omega
  have e2 : 2 ∣ n + 1 := by omega
  have e3 : 3 ∣ n + 1 := by clear h2 h3 e2 hn hn2; omega
  clear h2 h3' h3'' h3 hn hn2
  omega

/-- The first eight twin prime pairs. -/
theorem twin_primes_small :
    IsTwinPrimePair 3 ∧ IsTwinPrimePair 5 ∧ IsTwinPrimePair 11 ∧ IsTwinPrimePair 17 ∧
      IsTwinPrimePair 29 ∧ IsTwinPrimePair 41 ∧ IsTwinPrimePair 59 ∧ IsTwinPrimePair 71 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end Brockian.TwinPrimes

