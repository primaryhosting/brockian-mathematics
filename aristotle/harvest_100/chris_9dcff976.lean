import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime factor
congruent to `3` modulo `4`. -/
theorem exists_prime_factor_mod_four_eq_three :
    ∀ m : ℕ, m % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hm1 : m ≠ 1 := by omega
    have hpp : m.minFac.Prime := Nat.minFac_prime hm1
    have hpd : m.minFac ∣ m := Nat.minFac_dvd m
    have hpodd : m.minFac ≠ 2 := by
      intro h
      have h2 : (2 : ℕ) ∣ m := h ▸ hpd
      omega
    have hp2 : m.minFac % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hpodd)
    rcases Nat.lt_or_ge (m.minFac % 4) 2 with hlt | hge
    · -- `minFac m % 4 = 1`
      have hone : m.minFac % 4 = 1 := by omega
      obtain ⟨k, hk⟩ := hpd
      have hk4 : k % 4 = 3 := by
        have := Nat.mul_mod m.minFac k 4
        rw [← hk, hone, hm] at this
        omega
      have hkm : k < m := by
        have h2 : 2 ≤ m.minFac := hpp.two_le
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · simp [h] at hk; omega
          · exact h
        calc k = 1 * k := (one_mul k).symm
          _ < m.minFac * k := by
              exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl k) hk0
          _ = m := hk.symm
      obtain ⟨q, hq, hqd, hq4⟩ := ih k hkm hk4
      have hkd : k ∣ m := ⟨m.minFac, by rw [Nat.mul_comm]; exact hk⟩
      exact ⟨q, hq, hqd.trans hkd, hq4⟩
    · -- `minFac m % 4 = 3`
      exact ⟨m.minFac, hpp, hpd, by omega⟩

/-- **There are infinitely many primes congruent to `3` modulo `4`.**
For every `N` there is a prime `p` with `N < p` and `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  have hfac : 1 ≤ Nat.factorial N := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  set M : ℕ := 4 * Nat.factorial N - 1 with hM
  have hM4 : M % 4 = 3 := by
    obtain ⟨t, ht⟩ : ∃ t, Nat.factorial N = t + 1 := ⟨Nat.factorial N - 1, by omega⟩
    rw [hM, ht]
    omega
  obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_factor_mod_four_eq_three M hM4
  refine ⟨p, hp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  have hpdvd : p ∣ Nat.factorial N := Nat.dvd_factorial hp.pos hle
  have h1 : p ∣ 4 * Nat.factorial N := hpdvd.mul_left 4
  have hone : p ∣ 1 := by
    have hsub : 4 * Nat.factorial N - M = 1 := by omega
    simpa [hsub] using Nat.dvd_sub h1 hpd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- The set of primes congruent to `3` modulo `4` is infinite. -/
theorem infinite_setOf_prime_mod_four_eq_three :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hpN, hp4⟩ := infinitude_primes_4k3 N
  exact absurd (hN (show p ∈ {p : ℕ | p.Prime ∧ p % 4 = 3} from ⟨hp, hp4⟩)) (by omega)

end NumberTheory

