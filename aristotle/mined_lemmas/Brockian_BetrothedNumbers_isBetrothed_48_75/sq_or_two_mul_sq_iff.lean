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

open Finset ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
two distinct positive integers each of whose sum of *proper* divisors is one more
than the other, i.e. `σ m = σ n = m + n + 1`. -/

theorem sq_or_two_mul_sq_iff {n : ℕ} (hn : n ≠ 0) :
    (∃ a, n = a ^ 2 ∨ n = 2 * a ^ 2) ↔ ∀ p, p ≠ 2 → Even (n.factorization p) := by
  have h2p : ∀ p : ℕ, p ≠ 2 → (Nat.factorization 2) p = 0 := by
    intro p hp
    rw [Nat.Prime.factorization Nat.prime_two]
    simp [Ne.symm hp]
  constructor
  · rintro ⟨a, ha | ha⟩ p hp
    · subst ha
      rw [Nat.factorization_pow]
      exact ⟨a.factorization p, by simp [two_mul]⟩
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
      subst ha
      rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 ha0), Nat.factorization_pow]
      simp only [Finsupp.add_apply, h2p p hp, zero_add, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨a.factorization p, by ring⟩
  · intro h
    rcases Nat.even_or_odd (n.factorization 2) with he | ho
    · obtain ⟨t, ht⟩ := exists_sq_of_even_factorization hn (fun p => by
        rcases eq_or_ne p 2 with rfl | hp
        · exact he
        · exact h p hp)
      exact ⟨t, Or.inl ht⟩
    · have h2 : 2 ∣ n := by
        refine (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mpr ?_
        rcases Nat.eq_zero_or_pos (n.factorization 2) with h0 | h0
        · rw [h0] at ho; simp at ho
        · exact h0
      obtain ⟨k, hk⟩ := h2
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hn hk
      have hfac : n.factorization = (Nat.factorization 2) + k.factorization := by
        rw [hk, Nat.factorization_mul (by norm_num) hk0]
      obtain ⟨t, ht⟩ := exists_sq_of_even_factorization hk0 (fun p => by
        rcases eq_or_ne p 2 with rfl | hp
        · have hval : n.factorization 2 = 1 + k.factorization 2 := by
            rw [hfac]
            simp [Nat.Prime.factorization Nat.prime_two]
          rw [Nat.odd_iff] at ho
          rw [Nat.even_iff]
          omega
        · have hnp : n.factorization p = k.factorization p := by
            rw [hfac]; simp [h2p p hp]
          rw [← hnp]
          exact h p hp)
      exact ⟨t, Or.inr (by rw [hk, ht])⟩

/-- **Parity of the sum of divisors**: `σ n` is odd exactly when `n` is a square
or twice a square. -/
