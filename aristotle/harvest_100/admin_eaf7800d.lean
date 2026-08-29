/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Key step: any natural number congruent to `3` modulo `4` has a prime factor
congruent to `3` modulo `4`. -/
theorem exists_prime_factor_three_mod_four {n : ℕ} (hn : n % 4 = 3) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn1 : 1 < n := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    obtain ⟨m, rfl⟩ := hpd
    have hp2 : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp with h | h
      · subst h; omega
      · exact h
    have hm2 : m % 2 = 1 := by
      by_contra h
      have h2 : (2 : ℕ) ∣ m := by omega
      obtain ⟨t, ht⟩ := h2.mul_left p
      omega
    -- p % 4 ∈ {1, 3}, m % 4 ∈ {1, 3}
    have hpm : (p * m) % 4 = (p % 4) * (m % 4) % 4 := by
      conv_lhs => rw [Nat.mul_mod]
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hp4 with h1 | h1
    · -- p ≡ 1, so m ≡ 3
      have hm3 : m % 4 = 3 := by
        rcases hm4 with h2 | h2
        · rw [h1, h2] at hpm; omega
        · exact h2
      have hmlt : m < p * m := by
        have hm0 : 0 < m := by omega
        have : 1 < p := hp.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < p * m := (Nat.mul_lt_mul_right hm0).mpr this
      obtain ⟨q, hq, hqd, hq3⟩ := ih m hmlt hm3
      exact ⟨q, hq, hqd.mul_left p, hq3⟩
    · exact ⟨p, hp, Dvd.intro m rfl, h1⟩

/-- There are infinitely many primes congruent to `3` modulo `4`:
for every `N` there is a prime `p` with `N < p` and `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p, Nat.Prime p ∧ N < p ∧ p % 4 = 3 := by
  -- Euclid-style: consider `M = 4 * (N+1)! - 1`, which is `≡ 3 mod 4`.
  set K := (N + 1).factorial with hKdef
  have hK : 1 ≤ K := (N + 1).factorial_pos
  have hM4 : (4 * K - 1) % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hp3⟩ := exists_prime_factor_three_mod_four hM4
  refine ⟨p, hp, ?_, hp3⟩
  by_contra hle
  push_neg at hle
  have hpK : p ∣ K := Nat.dvd_factorial hp.pos (by omega)
  have h4K : p ∣ 4 * K := hpK.mul_left 4
  have h1 : p ∣ 1 := by
    have := Nat.dvd_sub h4K hpd
    simpa [Nat.sub_sub_self (by omega : 1 ≤ 4 * K)] using this
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h1)

/-- Restatement: the set of primes congruent to `3` modulo `4` is infinite. -/
theorem infinite_setOf_primes_4k3 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite :=
  Set.infinite_of_forall_exists_gt fun N => by
    obtain ⟨p, hp, hlt, hmod⟩ := infinitude_primes_4k3 N
    exact ⟨p, ⟨hp, hmod⟩, hlt⟩

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

