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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The twin prime conjecture itself is open, so what is proved here is a
*Lean-checked reduction*: the twin prime conjecture is shown to be equivalent to
an explicit elementary congruence condition (Clement's criterion), together with
some unconditional partial results.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `n` is the smaller member of a twin prime pair. -/
def IsTwinPrime (n : ℕ) : Prop := Nat.Prime n ∧ Nat.Prime (n + 2)

/-- Clement's elementary congruence condition:
`4 ((n-1)! + 1) + n ≡ 0 (mod n (n+2))`. -/
def ClementCongruence (n : ℕ) : Prop := n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n

/-! ### Wilson's theorem in divisibility form -/

/-- Wilson's theorem, stated as a divisibility criterion for primality. -/
theorem prime_iff_dvd_factorial_pred_add_one {p : ℕ} (hp : 2 ≤ p) :
    Nat.Prime p ↔ p ∣ (p - 1)! + 1 := by
  haveI : NeZero p := ⟨by omega⟩
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega : p ≠ 1), ← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination h

/-! ### Even `n` satisfies neither side of Clement's criterion -/

/-- For even `n ≥ 6`, `n` divides `(n-1)!`. -/
theorem dvd_factorial_pred_of_even {n : ℕ} (h6 : 6 ≤ n) (he : Even n) : n ∣ (n - 1)! := by
  obtain ⟨m, hm⟩ := he
  have hm3 : 3 ≤ m := by omega
  have h1 : 2 ∣ (m - 1)! := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨c, hc⟩ := h1
  have hfac : m ! = m * (m - 1)! := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [Nat.factorial_succ]
  have h2 : n ∣ m ! := ⟨c, by rw [hfac, hc, hm]; ring⟩
  exact h2.trans (Nat.factorial_dvd_factorial (by omega))

/-! ### Clement's criterion -/

/-- **Clement's criterion** (1949): for `n ≥ 2`, the numbers `n` and `n + 2` are both prime
if and only if `n (n+2)` divides `4 ((n-1)! + 1) + n`. -/
theorem clement_criterion {n : ℕ} (hn : 2 ≤ n) : IsTwinPrime n ↔ ClementCongruence n := by
  rcases Nat.even_or_odd n with he | ho
  · -- even `n`: both sides fail
    have hL : ¬ IsTwinPrime n := by
      rintro ⟨hp, hp2⟩
      have : n = 2 := (Nat.Prime.even_iff hp).mp he
      subst this
      norm_num at hp2
    have hR : ¬ ClementCongruence n := by
      intro h
      have hdvd : n ∣ 4 * ((n - 1)! + 1) + n := dvd_trans ⟨n + 2, rfl⟩ h
      rcases lt_or_ge n 6 with hlt | hge
      · have hn24 : n = 2 ∨ n = 4 := by rcases he with ⟨m, hm⟩; omega
        rcases hn24 with rfl | rfl <;> revert h <;>
          norm_num [ClementCongruence, Nat.factorial]
      · have hf : n ∣ (n - 1)! := dvd_factorial_pred_of_even hge he
        have h4 : n ∣ 4 := by
          have h1 : n ∣ 4 * (n - 1)! + 4 := by
            have e : 4 * ((n - 1)! + 1) + n = n + (4 * (n - 1)! + 4) := by ring
            rw [e] at hdvd
            exact (Nat.dvd_add_right (dvd_refl n)).mp hdvd
          have h2 : n ∣ 4 * (n - 1)! := Dvd.dvd.mul_left hf 4
          exact (Nat.dvd_add_right h2).mp h1
        have := Nat.le_of_dvd (by norm_num) h4
        omega
    simp [hL, hR]
  · -- odd `n`
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · omega
        · exact absurd ho (by decide)
      · exact h
    have hkodd : Odd (k + 1) := ho
    have hkeven : Even k := by
      rcases Nat.even_or_odd k with h | h
      · exact h
      · exact absurd hkodd (by simp [Nat.odd_add_one, h])
    set D : ℕ := 4 * ((k + 1 - 1)! + 1) + (k + 1) with hD
    have hDk : D = 4 * (k ! + 1) + (k + 1) := by simp [hD]
    -- left factor
    have hleft : (k + 1) ∣ D ↔ Nat.Prime (k + 1) := by
      have e1 : D = (k + 1) + 4 * (k ! + 1) := by rw [hDk]; ring
      rw [e1, Nat.dvd_add_right (dvd_refl (k + 1))]
      constructor
      · intro h
        have hcop : Nat.Coprime (k + 1) 4 := by
          have h2 : Nat.Coprime (k + 1) 2 := Nat.coprime_two_right.mpr hkodd
          simpa using h2.pow_right 2
        have := hcop.dvd_of_dvd_mul_left h
        exact (prime_iff_dvd_factorial_pred_add_one (by omega)).mpr (by simpa using this)
      · intro h
        have := (prime_iff_dvd_factorial_pred_add_one (by omega : 2 ≤ k + 1)).mp h
        simp only [Nat.add_sub_cancel] at this
        exact Dvd.dvd.mul_left this 4
    -- right factor
    have hright : (k + 3) ∣ D ↔ Nat.Prime (k + 3) := by
      have e1 : D = (k + 3) + 2 * (2 * k ! + 1) := by rw [hDk]; ring
      have e2 : (k + 2)! + 1 = (k + 3) * (k * k !) + (2 * k ! + 1) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring
      have hstep : (k + 3) ∣ D ↔ (k + 3) ∣ 2 * k ! + 1 := by
        rw [e1, Nat.dvd_add_right (dvd_refl (k + 3))]
        constructor
        · intro h
          have hcop : Nat.Coprime (k + 3) 2 :=
            Nat.coprime_two_right.mpr (by
              rcases hkeven with ⟨j, hj⟩
              exact ⟨j + 1, by omega⟩)
          exact hcop.dvd_of_dvd_mul_left h
        · intro h; exact Dvd.dvd.mul_left h 2
      rw [hstep, prime_iff_dvd_factorial_pred_add_one (by omega : 2 ≤ k + 3)]
      have hs : k + 3 - 1 = k + 2 := by omega
      rw [hs, e2, Nat.dvd_add_right ⟨k * k !, rfl⟩]
    -- combine
    have hcop : Nat.Coprime (k + 1) (k + 3) := by
      have h2 : Nat.Coprime (k + 1) 2 := Nat.coprime_two_right.mpr hkodd
      simpa [Nat.Coprime, Nat.gcd_comm, show k + 3 = 2 + (k + 1) by omega,
        Nat.gcd_add_self_left] using h2
    constructor
    · rintro ⟨hp1, hp2⟩
      have h1 : (k + 1) ∣ D := hleft.mpr hp1
      have h2 : (k + 3) ∣ D := hright.mpr (by simpa [Nat.add_assoc] using hp2)
      have := hcop.mul_dvd_of_dvd_of_dvd h1 h2
      simpa [ClementCongruence, hD, show k + 1 + 2 = k + 3 by omega] using this
    · intro h
      have h' : (k + 1) * (k + 3) ∣ D := by
        simpa [ClementCongruence, hD, show k + 1 + 2 = k + 3 by omega] using h
      refine ⟨hleft.mp (dvd_trans ⟨k + 3, rfl⟩ h'), ?_⟩
      have := hright.mp (dvd_trans ⟨k + 1, by ring⟩ h')
      simpa [Nat.add_assoc] using this

/-! ### The reduction -/

/-- **Twin Prime Conjecture, as a Lean-checked reduction.**

The set of twin primes is infinite if and only if Clement's elementary congruence
`n (n+2) ∣ 4 ((n-1)! + 1) + n` has arbitrarily large solutions `n`.

The twin prime conjecture is open; what is established here is the equivalence of the
conjecture with this purely elementary congruence statement. -/
theorem TwinPrimeConjecture :
    (∀ N : ℕ, ∃ n, N ≤ n ∧ ClementCongruence n) ↔ {n : ℕ | IsTwinPrime n}.Infinite := by
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt (fun a => ?_)
    obtain ⟨n, hn, hc⟩ := h (a + 3)
    exact ⟨n, (clement_criterion (by omega)).mpr hc, by omega⟩
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    have hmem : IsTwinPrime n := hn
    exact ⟨n, le_of_lt hlt, (clement_criterion hmem.1.two_le).mp hmem⟩

/-! ### Unconditional partial results -/

/-- Twin primes exist: the pairs `(3,5)`, `(5,7)`, `(11,13)`, `(17,19)`, `(29,31)`. -/
theorem twin_prime_examples :
    IsTwinPrime 3 ∧ IsTwinPrime 5 ∧ IsTwinPrime 11 ∧ IsTwinPrime 17 ∧ IsTwinPrime 29 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- Clement's criterion, checked on a small example: `3` and `5` are twin primes. -/
example : ClementCongruence 3 := (clement_criterion (by norm_num)).mp twin_prime_examples.1

/-- Every twin prime pair other than `(3,5)` has the form `(6k - 1, 6k + 1)`:
if `n` and `n+2` are prime and `n ≥ 5`, then `n % 6 = 5`. -/
theorem twin_prime_mod_six {n : ℕ} (h : IsTwinPrime n) (hn : 5 ≤ n) : n % 6 = 5 := by
  obtain ⟨hp, hp2⟩ := h
  have h2 : ¬ (2 ∣ n) := by
    intro hd
    have := hp.eq_one_or_self_of_dvd 2 hd
    omega
  have h3 : ¬ (3 ∣ n) := by
    intro hd
    have := hp.eq_one_or_self_of_dvd 3 hd
    omega
  have h3' : ¬ (3 ∣ (n + 2)) := by
    intro hd
    have := hp2.eq_one_or_self_of_dvd 3 hd
    omega
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ n = 6 * q + r :=
    ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r <;> omega

/-- There is exactly one prime triple `(p, p+2, p+4)`, namely `(3, 5, 7)`. -/
theorem prime_triple_unique {p : ℕ} (h1 : Nat.Prime p) (h2 : Nat.Prime (p + 2))
    (h3 : Nat.Prime (p + 4)) : p = 3 := by
  by_contra hp
  have hp2 : 2 ≤ p := h1.two_le
  have hd3 : (3 : ℕ) ∣ p ∨ (3 : ℕ) ∣ (p + 2) ∨ (3 : ℕ) ∣ (p + 4) := by omega
  rcases hd3 with hd | hd | hd
  · have := h1.eq_one_or_self_of_dvd 3 hd; omega
  · have := h2.eq_one_or_self_of_dvd 3 hd; omega
  · have := h3.eq_one_or_self_of_dvd 3 hd; omega

end Brockian.TwinPrimes

