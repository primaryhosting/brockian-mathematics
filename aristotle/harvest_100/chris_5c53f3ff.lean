/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime factor congruent to `3`
modulo `4`.  Indeed such a number is odd, and a product of primes all congruent to `1`
modulo `4` is again congruent to `1` modulo `4`. -/
theorem exists_prime_factor_mod_four_eq_three :
    ∀ m : ℕ, m % 4 = 3 → ∃ p, Nat.Prime p ∧ p ∣ m ∧ p % 4 = 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hm1 : m ≠ 1 := by omega
    obtain ⟨q, hq, k, hk⟩ := Nat.exists_prime_and_dvd hm1
    have hq2 : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · subst h
        omega
      · exact h
    have hqmod : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hqmod with h1 | h3
    · -- `q ≡ 1 [MOD 4]`, so the cofactor `k` is still `≡ 3 [MOD 4]`, and is smaller.
      have hkmod : k % 4 = 3 := by
        have : m % 4 = (q % 4) * (k % 4) % 4 := by rw [hk, Nat.mul_mod]
        rw [h1, one_mul, Nat.mod_mod_of_dvd] at this
        · omega
        · norm_num
      have hklt : k < m := by
        have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hm
        have hq2' : 2 ≤ q := hq.two_le
        have : 1 * k < q * k :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hk0)).mpr (by omega)
        omega
      obtain ⟨p, hp, hpd, hpm⟩ := ih k hklt hkmod
      exact ⟨p, hp, hk ▸ hpd.mul_left q, hpm⟩
    · exact ⟨q, hq, ⟨k, hk⟩, h3⟩

/-- **There are infinitely many primes congruent to `3` modulo `4`**: for every `N` there is
a prime `p` with `N < p` and `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p, Nat.Prime p ∧ N < p ∧ p % 4 = 3 := by
  set n := max N 3 with hn
  have hfac : 1 ≤ Nat.factorial n := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  set m := 4 * Nat.factorial n - 1 with hmdef
  have hmmod : m % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hpm⟩ := exists_prime_factor_mod_four_eq_three m hmmod
  refine ⟨p, hp, ?_, hpm⟩
  by_contra hle
  push_neg at hle
  have hpn : p ≤ n := le_trans hle (le_max_left N 3)
  have hpfac : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos hpn
  have h4 : p ∣ 4 * Nat.factorial n := hpfac.mul_left 4
  have h1 : p ∣ 1 := by
    have := Nat.dvd_sub h4 hpd
    have heq : 4 * Nat.factorial n - m = 1 := by omega
    rwa [heq] at this
  exact absurd (Nat.dvd_one.mp h1) hp.one_lt.ne'

/-- Restatement of the infinitude of primes `≡ 3 [MOD 4]` as the infinitude of a set. -/
theorem infinite_setOf_primes_4k3 : {p : ℕ | Nat.Prime p ∧ p % 4 = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hlt, hmod⟩ := infinitude_primes_4k3 N
  exact absurd (hN ⟨hp, hmod⟩) (by omega)

end NumberTheory

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

