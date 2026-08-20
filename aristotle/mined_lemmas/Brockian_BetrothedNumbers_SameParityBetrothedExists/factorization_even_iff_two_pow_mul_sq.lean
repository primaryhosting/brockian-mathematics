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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- A *betrothed* (quasi-amicable) pair: two distinct positive numbers each of whose
sum of divisors equals `m + n + 1`. -/

theorem factorization_even_iff_two_pow_mul_sq {n : ℕ} (hn : n ≠ 0) :
    (∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p)) ↔ ∃ a k, n = 2 ^ a * k ^ 2 := by
  constructor
  · intro h
    obtain ⟨s, b, hab, hsf⟩ := Nat.sq_mul_squarefree n
    have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
    have hs0 : s ≠ 0 := hsf.ne_zero
    have hfac : ∀ p, n.factorization p = 2 * b.factorization p + s.factorization p := by
      intro p
      rw [← hab, Nat.factorization_mul (by positivity) hs0]
      simp [Nat.factorization_pow, two_mul]
    have key : ∀ p, p.Prime → p ∣ s → p = 2 := by
      intro p hp hps
      by_contra hne
      have hpn : p ∣ n := hab ▸ hps.mul_left _
      have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩
      have h1 : s.factorization p = 1 := by
        have hle := Squarefree.natFactorization_le_one p hsf
        have hge := hp.factorization_pos_of_dvd hs0 hps
        omega
      have hev := h p hmem hne
      rw [hfac, h1] at hev
      simp [parity_simps] at hev
    have hs2 : s = 1 ∨ s = 2 := by
      have h4 : ¬ (4 ∣ s) := by
        intro h4
        have := hsf 2 (by omega : (2 : ℕ) * 2 ∣ s)
        simp at this
      rcases eq_or_ne s 1 with h1 | h1
      · exact Or.inl h1
      · obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd h1
        have hp2 := key p hp hps
        subst hp2
        right
        obtain ⟨t, rfl⟩ := hps
        have ht : ¬ (2 ∣ t) := by
          rintro ⟨u, rfl⟩; exact h4 ⟨u, by ring⟩
        have ht1 : t = 1 := by
          by_contra htne
          obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd htne
          exact ht ((key q hq (hqt.mul_left 2)) ▸ hqt)
        simp [ht1]
    rcases hs2 with rfl | rfl
    · exact ⟨0, b, by simpa using hab.symm⟩
    · exact ⟨1, b, by rw [← hab]; ring⟩
  · rintro ⟨a, k, rfl⟩ p hp hp2
    have hk0 : k ≠ 0 := by rintro rfl; simp at hn
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h2 : ((2 : ℕ) ^ a).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hd))
    have h3 : (2 ^ a * k ^ 2).factorization p = 2 * k.factorization p := by
      rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hk0),
        Finsupp.add_apply, h2, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, zero_add]
    rw [h3]
    exact even_two_mul _

/-- `σ n` is odd exactly when `n` is a square or twice a square. -/
