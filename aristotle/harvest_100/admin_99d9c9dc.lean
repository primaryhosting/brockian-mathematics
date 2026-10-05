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

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/
def TwinPrimeConjecture : Prop :=
  ∀ n : ℕ, ∃ p : ℕ, n < p ∧ p.Prime ∧ (p + 2).Prime

/-- The set of twin primes (the smaller member of each twin pair). -/
def twinPrimes : Set ℕ := {p : ℕ | p.Prime ∧ (p + 2).Prime}

/-- The twin prime conjecture is equivalent to the infinitude of the set of twin primes. -/
theorem twinPrimeConjecture_iff_infinite : TwinPrimeConjecture ↔ twinPrimes.Infinite := by
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    obtain ⟨p, hp, hp1, hp2⟩ := h a
    exact ⟨p, Set.mem_setOf_eq ▸ ⟨hp1, hp2⟩, hp⟩
  · intro h n
    obtain ⟨p, hp, hpn⟩ := h.exists_gt n
    exact ⟨p, hpn, hp.1, hp.2⟩

/-- Contrapositive form: the twin prime conjecture fails exactly when some bound `N`
cuts off all twin primes. -/
theorem not_twinPrimeConjecture_iff :
    ¬ TwinPrimeConjecture ↔ ∃ N : ℕ, ∀ p : ℕ, N < p → ¬ (p.Prime ∧ (p + 2).Prime) := by
  unfold TwinPrimeConjecture
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp hpp => (hN p hp hpp.1) hpp.2⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp hpp hpp2 => hN p hp ⟨hpp, hpp2⟩⟩

/-! ## Wilson's theorem in divisibility form -/

/-- Wilson's theorem, stated with divisibility of natural numbers:
for `n > 1`, `n` is prime iff `n ∣ (n-1)! + 1`. -/
theorem prime_iff_dvd_factorial_succ {n : ℕ} (hn : 1 < n) :
    n.Prime ↔ n ∣ (n - 1)! + 1 := by
  have hbridge : (n ∣ (n - 1)! + 1) ↔ (((n - 1)! : ZMod n) = -1) := by
    constructor
    · intro h
      have h0 : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      push_cast at h0
      linear_combination h0
    · intro h
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [h]
      ring
  rw [hbridge, Nat.prime_iff]
  exact ⟨fun h => (Nat.prime_iff_fac_equiv_neg_one hn.ne').mp h,
    fun h => Nat.prime_of_fac_equiv_neg_one h hn.ne'⟩

/-! ## Elementary factorial facts -/

/-- `(n+1)! = 2 * (n-1)! + (n+2) * ((n-1) * (n-1)!)`, valid for `n ≥ 1`. -/
theorem factorial_succ_succ_identity {n : ℕ} (hn : 1 ≤ n) :
    (n + 1)! = 2 * (n - 1)! + (n + 2) * ((n - 1) * (n - 1)!) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  ring

/-- For `0 < a < b ≤ N` we have `a * b ∣ N !`. -/
theorem mul_dvd_factorial_of_lt {a b N : ℕ} (ha : 0 < a) (hab : a < b) (hbN : b ≤ N) :
    a * b ∣ N ! := by
  have hb : b = (b - 1) + 1 := by omega
  have h1 : a * b ∣ b ! := by
    rw [hb, Nat.factorial_succ, ← hb]
    exact mul_comm a b ▸ Nat.mul_dvd_mul (dvd_refl b) (Nat.dvd_factorial ha (by omega))
  exact h1.trans (Nat.factorial_dvd_factorial hbN)

/-- If `n` is even and `n ≥ 6`, then `n ∣ (n-1)!`. -/
theorem dvd_factorial_pred_of_even {n : ℕ} (hev : 2 ∣ n) (hn : 6 ≤ n) : n ∣ (n - 1)! := by
  obtain ⟨k, rfl⟩ := hev
  have hk : 3 ≤ k := by omega
  have h1 : k * (2 * k - 2) ∣ (2 * k - 1)! :=
    mul_dvd_factorial_of_lt (by omega) (by omega) (le_refl _)
  refine dvd_trans ?_ h1
  refine ⟨k - 1, ?_⟩
  have h2 : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [h2]
  ring

/-! ## Clement's criterion -/

/-- **Clement's theorem**: for `n > 1`, the pair `(n, n+2)` is a twin prime pair if and only if
`n * (n + 2)` divides `4 * ((n-1)! + 1) + n`. -/
theorem clement_criterion {n : ℕ} (hn : 1 < n) :
    (n.Prime ∧ (n + 2).Prime) ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  obtain ⟨F, hF⟩ : ∃ F, (n - 1)! = F := ⟨_, rfl⟩
  have hident : 2 * F + (n + 2) * ((n - 1) * F) = (n + 1)! := by
    rw [← hF]; exact (factorial_succ_succ_identity (by omega)).symm
  have hsub : (n + 2) - 1 = n + 1 := by omega
  rw [hF]
  constructor
  · rintro ⟨hp, hq⟩
    -- `n` must be odd
    have hne2 : n ≠ 2 := by
      rintro rfl
      norm_num at hq
    have hodd : ¬ (2 ∣ n) := by
      intro h2
      exact hne2 ((Nat.Prime.eq_one_or_self_of_dvd hp 2 h2).resolve_left (by norm_num)).symm
    -- Wilson for `n`
    have h1 : n ∣ F + 1 := by
      have := (prime_iff_dvd_factorial_succ hn).mp hp
      rwa [hF] at this
    -- Wilson for `n + 2`
    have h2 : (n + 2) ∣ (n + 1)! + 1 := by
      have := (prime_iff_dvd_factorial_succ (n := n + 2) (by omega)).mp hq
      rwa [hsub] at this
    have h3 : (n + 2) ∣ 2 * F + 1 := by
      rw [← hident] at h2
      have h4 : (n + 2) ∣ (n + 2) * ((n - 1) * F) := Dvd.intro _ rfl
      have h5 := Nat.dvd_sub' h2 h4
      have h6 : 2 * F + (n + 2) * ((n - 1) * F) + 1 - (n + 2) * ((n - 1) * F) = 2 * F + 1 := by
        omega
      rwa [h6] at h5
    -- combine the two divisibilities
    have hdn : n ∣ 4 * (F + 1) + n := Dvd.dvd.add (Dvd.dvd.mul_left h1 4) (dvd_refl n)
    have hdn2 : (n + 2) ∣ 4 * (F + 1) + n := by
      have h5 : 4 * (F + 1) + n = 2 * (2 * F + 1) + (n + 2) := by ring
      rw [h5]
      exact Dvd.dvd.add (Dvd.dvd.mul_left h3 2) (dvd_refl _)
    have hcop2 : Nat.Coprime n 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    have hcop : Nat.Coprime n (n + 2) := by
      have : Nat.gcd n (n + 2) = Nat.gcd n 2 := by
        rw [Nat.add_comm, Nat.gcd_comm n (2 + n), Nat.gcd_add_self_right, Nat.gcd_comm]
      exact (Nat.Coprime) ▸ (by rw [Nat.Coprime, this]; exact hcop2)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdn hdn2
  · intro h
    have hdn : n ∣ 4 * (F + 1) := by
      have h1 : n ∣ 4 * (F + 1) + n := dvd_trans (Dvd.intro _ rfl) h
      have h2 := Nat.dvd_sub' h1 (dvd_refl n)
      rwa [Nat.add_sub_cancel] at h2
    have hdn2 : (n + 2) ∣ 2 * (2 * F + 1) := by
      have h1 : (n + 2) ∣ 4 * (F + 1) + n := dvd_trans (Dvd.intro_left _ rfl) h
      have h5 : 4 * (F + 1) + n = 2 * (2 * F + 1) + (n + 2) := by ring
      rw [h5] at h1
      have h2 := Nat.dvd_sub' h1 (dvd_refl (n + 2))
      rwa [Nat.add_sub_cancel] at h2
    -- `n` must be odd
    have hodd : ¬ (2 ∣ n) := by
      intro hev
      rcases lt_or_ge n 6 with hlt | hge
      · interval_cases n <;> simp [Nat.factorial] at hF <;> omega
      · have hdF : n ∣ F := hF ▸ dvd_factorial_pred_of_even hev hge
        have h4 : n ∣ 4 := by
          have h6 : 4 * (F + 1) = 4 * F + 4 := by ring
          rw [h6] at hdn
          have h7 := Nat.dvd_sub' hdn (Dvd.dvd.mul_left hdF 4)
          rwa [Nat.add_sub_cancel_left] at h7
        have := Nat.le_of_dvd (by norm_num) h4
        omega
    have hcop2 : Nat.Coprime n 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    have hcop4 : Nat.Coprime n 4 := by
      have h8 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h8]
      exact hcop2.pow_right 2
    have hcop2' : Nat.Coprime (n + 2) 2 := by
      have hodd' : ¬ (2 ∣ (n + 2)) := by
        intro hc
        exact hodd (by omega)
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd').symm
    have hp : n.Prime := by
      refine (prime_iff_dvd_factorial_succ hn).mpr ?_
      rw [hF]
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop4 (by rw [mul_comm] at hdn; exact hdn)
    have hq : (n + 2).Prime := by
      refine (prime_iff_dvd_factorial_succ (n := n + 2) (by omega)).mpr ?_
      rw [hsub, ← hident]
      have h3 : (n + 2) ∣ 2 * F + 1 :=
        Nat.Coprime.dvd_of_dvd_mul_left hcop2' (by rw [mul_comm] at hdn2; exact hdn2)
      have h9 : 2 * F + (n + 2) * ((n - 1) * F) + 1 = (2 * F + 1) + (n + 2) * ((n - 1) * F) := by
        ring
      rw [h9]
      exact Dvd.dvd.add h3 (Dvd.intro _ rfl)
    exact ⟨hp, hq⟩

/-- The twin prime conjecture, restated by Clement's criterion as a purely
factorial-divisibility statement. -/
theorem twinPrimeConjecture_iff_clement :
    TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  constructor
  · intro h N
    obtain ⟨p, hp, hp1, hp2⟩ := h N
    exact ⟨p, hp, (clement_criterion hp1.one_lt).mp ⟨hp1, hp2⟩⟩
  · intro h N
    obtain ⟨n, hn, hd⟩ := h (max N 1)
    have hn1 : 1 < n := lt_of_le_of_lt (le_max_right N 1) hn
    obtain ⟨hp, hq⟩ := (clement_criterion hn1).mpr hd
    exact ⟨n, lt_of_le_of_lt (le_max_left N 1) hn, hp, hq⟩

/-! ## An unconditional partial result -/

/-- Every twin prime pair beyond `(3,5)` has its smaller member congruent to `5` mod `6`. -/
theorem twin_prime_mod_six {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h) (by omega)
  have h3' : ¬ (3 ∣ p) := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h) (by omega)
  have h3'' : ¬ (3 ∣ (p + 2)) := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h) (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at h2 h3' h3''
  omega

/-- There is at least one twin prime pair. -/
theorem exists_twinPrime : ∃ p : ℕ, p.Prime ∧ (p + 2).Prime :=
  ⟨3, by norm_num⟩

end Brockian.TwinPrimes

