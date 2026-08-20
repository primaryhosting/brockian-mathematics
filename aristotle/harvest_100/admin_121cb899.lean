import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime divisor that is itself
congruent to `3` modulo `4`.

Indeed such a number is odd, so all of its prime factors are odd; if all of them were
congruent to `1` modulo `4`, so would be their product. -/
theorem exists_prime_dvd_mod_four_eq_three :
    ∀ m : ℕ, m % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hm1 : m ≠ 1 := by omega
    obtain ⟨q, hq, k, rfl⟩ := Nat.exists_prime_and_dvd hm1
    have hk0 : k ≠ 0 := by rintro rfl; simp at hm
    have hq2 : q ≠ 2 := by rintro rfl; omega
    have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
      have := hq.eq_two_or_odd
      omega
    rcases hq4 with h | h
    · have hmod : q * k % 4 = k % 4 := by
        rw [Nat.mul_mod, h, one_mul, Nat.mod_mod_of_dvd]
        exact ⟨1, rfl⟩
      have hk : k % 4 = 3 := by omega
      have hklt : k < q * k :=
        (lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hk0)).mpr hq.one_lt
      obtain ⟨p, hp, hpd, hp4⟩ := ih k hklt hk
      exact ⟨p, hp, hpd.mul_left q, hp4⟩
    · exact ⟨q, hq, Dvd.intro k rfl, h⟩

/-- **There are infinitely many primes congruent to `3` modulo `4`**: for every `N` there
exists a prime `p` with `N < p` and `p % 4 = 3`.

Euclid-style argument: the number `4 * N ! - 1` is congruent to `3` modulo `4`, hence it has
a prime divisor `p` with `p % 4 = 3`; such a `p` cannot be `≤ N`, since otherwise it would
divide `N !` and therefore also divide `1`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  have hfac : 1 ≤ Nat.factorial N := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  set m := 4 * Nat.factorial N - 1 with hm_def
  have hm : m % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_dvd_mod_four_eq_three m hm
  refine ⟨p, hp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  have hpf : p ∣ Nat.factorial N := Nat.dvd_factorial hp.pos hle
  have h4 : p ∣ 4 * Nat.factorial N := hpf.mul_left 4
  have hsub : p ∣ 4 * Nat.factorial N - m := Nat.dvd_sub h4 hpd
  have h1 : 4 * Nat.factorial N - m = 1 := by omega
  rw [h1] at hsub
  exact hp.one_lt.ne' (Nat.dvd_one.mp hsub)

/-- The set of primes congruent to `3` modulo `4` is infinite. -/
theorem infinite_setOf_prime_mod_four_eq_three :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hpN, hp4⟩ := infinitude_primes_4k3 N
  have hle : p ≤ N := hN (show p ∈ {p : ℕ | p.Prime ∧ p % 4 = 3} from ⟨hp, hp4⟩)
  omega

/-- The same statement, obtained instead from Mathlib's version of Dirichlet's theorem on
primes in arithmetic progressions, `Nat.forall_exists_prime_gt_and_modEq`. -/
theorem infinitude_primes_4k3_via_dirichlet (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3) (by norm_num) (by decide)
  exact ⟨p, hp, hpN, by simpa [Nat.ModEq] using hmod⟩

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

