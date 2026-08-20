/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-! ### An elementary Euclid-style argument

Every natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`,
because a product of numbers congruent to `1` mod `4` is again congruent to `1` mod `4`.
Applying this to `4 * N ! - 1` produces a prime `> N` congruent to `3` mod `4`. -/

/-- If `q ≡ 1 [MOD 4]` and `q * m ≡ 3 [MOD 4]`, then `m ≡ 3 [MOD 4]`. -/
private theorem mod_four_of_mul_left_one {q m : ℕ} (h1 : q % 4 = 1) (h3 : q * m % 4 = 3) :
    m % 4 = 3 := by
  rwa [Nat.mul_mod, h1, one_mul, Nat.mod_mod] at h3

/-- Any `n` with `n % 4 = 3` admits a prime divisor `p` with `p % 4 = 3`. -/
theorem exists_prime_factor_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨q, hq, m, hm⟩ : ∃ q, Nat.Prime q ∧ ∃ m, n = q * m :=
      ⟨n.minFac, Nat.minFac_prime hn1, (Nat.minFac_dvd n).choose,
        (Nat.minFac_dvd n).choose_spec⟩
    -- `n` is odd, hence so is any prime factor of it
    have hqdvd : q ∣ n := ⟨m, hm⟩
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h2 | h1
      · subst h2; omega
      · exact h1
    have hq1 : 1 < q := hq.one_lt
    rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h1 | h3
    · -- the prime factor is `1` mod `4`: pass to the strictly smaller cofactor
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · rw [Nat.mul_zero] at hm; omega
        · exact h
      have hmmod : m % 4 = 3 := mod_four_of_mul_left_one h1 (by rw [← hm]; exact hn)
      have hmlt : m < n := by rw [hm]; nlinarith
      obtain ⟨p, hp', hpd, hpm⟩ := ih m hmlt hmmod
      exact ⟨p, hp', hpd.trans ⟨q, by rw [hm, Nat.mul_comm]⟩, hpm⟩
    · exact ⟨q, hq, hqdvd, h3⟩

/-- **Infinitude of primes congruent to `3` mod `4`.**

For every `N` there is a prime `p` with `N < p` and `p % 4 = 3`.

Elementary Euclid-style proof: a prime factor `p ≡ 3 [MOD 4]` of `4 * N ! - 1` cannot be `≤ N`,
since such a prime divides `N !` and hence would divide `1`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p, N < p ∧ Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨F, hF1, hFdvd⟩ : ∃ F : ℕ, 1 ≤ F ∧ ∀ p : ℕ, Nat.Prime p → p ≤ N → p ∣ F :=
    ⟨Nat.factorial N, Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _),
      fun p hp hpN => Nat.dvd_factorial hp.pos hpN⟩
  have hnmod : (4 * F - 1) % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hpmod⟩ := exists_prime_factor_mod_four_eq_three _ hnmod
  refine ⟨p, ?_, hp, hpmod⟩
  by_contra hle
  push_neg at hle
  have h4 : p ∣ 4 * F := (hFdvd p hp hle).mul_left 4
  have h1 : p ∣ 1 := by
    have h := Nat.dvd_sub h4 hpd
    rwa [Nat.sub_sub_self (by omega : 1 ≤ 4 * F)] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The same statement obtained instead from Mathlib's theorem on primes in arithmetic
progressions, `Nat.forall_exists_prime_gt_and_modEq` (Dirichlet). -/
theorem infinitude_primes_4k3' (N : ℕ) : ∃ p, N < p ∧ Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3) (by norm_num) (by decide)
  exact ⟨p, hpN, hp, by simpa [Nat.ModEq] using hmod⟩

/-- Equivalent phrasing: the set of primes congruent to `3` mod `4` is infinite. -/
theorem infinite_setOf_prime_mod_four_eq_three :
    {p : ℕ | Nat.Prime p ∧ p % 4 = 3}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hpN, hp, hpmod⟩ := infinitude_primes_4k3 N
  have : p ≤ N := hN ⟨hp, hpmod⟩
  omega

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

