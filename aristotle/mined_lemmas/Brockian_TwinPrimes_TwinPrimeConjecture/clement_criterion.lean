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
