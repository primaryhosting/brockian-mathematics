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

/-- Any natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`. -/
theorem exists_prime_factor_three_mod_four :
    ∀ m : ℕ, m % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hm1 : m ≠ 1 := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hm1
    -- `p` is odd, since `m` is odd
    have hmodd : m % 2 = 1 := by omega
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · exfalso
        subst h2
        obtain ⟨c, rfl⟩ := hpd
        omega
      · exact h2
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with hp4 | hp4
    · -- `p ≡ 1 [MOD 4]`: pass to the cofactor
      obtain ⟨q, rfl⟩ := hpd
      have hq4 : q % 4 = 3 := by
        have := Nat.mul_mod p q 4
        rw [hp4] at this
        omega
      have hqlt : q < p * q := by
        have hq0 : 0 < q := by omega
        have hp2 : 2 ≤ p := hp.two_le
        calc q = 1 * q := (one_mul q).symm
        _ < p * q := by exact Nat.mul_lt_mul_of_lt_of_le hp2 (le_refl q) hq0
      obtain ⟨r, hr, hrd, hr4⟩ := ih q hqlt hq4
      exact ⟨r, hr, hrd.mul_left p, hr4⟩
    · exact ⟨p, hp, hpd, hp4⟩

/-- **Infinitude of primes congruent to 3 mod 4**: for every `N` there is a prime `p > N`
with `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  have hfac : 1 ≤ Nat.factorial N := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  set m : ℕ := 4 * (Nat.factorial N - 1) + 3 with hm
  have hm4 : m % 4 = 3 := by simp [hm]
  have hmsucc : m + 1 = 4 * Nat.factorial N := by
    have : 4 * (Nat.factorial N - 1) = 4 * Nat.factorial N - 4 := by omega
    omega
  obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_factor_three_mod_four m hm4
  refine ⟨p, hp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  have hpf : p ∣ Nat.factorial N := Nat.dvd_factorial hp.pos hle
  have h4 : p ∣ m + 1 := by rw [hmsucc]; exact hpf.mul_left 4
  have h1 : p ∣ 1 := by
    have := Nat.dvd_sub h4 hpd
    simpa using this
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The set of primes congruent to `3` mod `4` is infinite. -/
theorem infinite_setOf_prime_and_three_mod_four :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hNp, hp4⟩ := infinitude_primes_4k3 N
  exact absurd (hN (show p ∈ {p : ℕ | p.Prime ∧ p % 4 = 3} from ⟨hp, hp4⟩)) (by omega)

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

