/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- rendered as a plain block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 400000
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

namespace Brockian

/-- A kernel-friendly primality test: trial division by all candidate divisors `< 47`.
It is a correct primality test for every `n < 47 ^ 2 = 2209`, see `Brockian.isPSmall_iff`. -/
def isPSmall (n : ℕ) : Bool :=
  2 ≤ n && (List.range 47).all (fun m => m < 2 || n ≤ m || n % m != 0)

/-- Unfolding of `Brockian.isPSmall` into a quantified arithmetic statement. -/
theorem isPSmall_eq_true_iff (n : ℕ) :
    isPSmall n = true ↔ (2 ≤ n ∧ ∀ m, m < 47 → 2 ≤ m → m < n → n % m ≠ 0) := by
  simp only [isPSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm h2m hmn => ?_⟩
    rcases h2 m hm with (h | h) | h <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases h2m : 2 ≤ m
    · by_cases hmn : m < n
      · exact Or.inr (h2 m hm h2m hmn)
      · exact Or.inl (Or.inr (by omega))
    · exact Or.inl (Or.inl (by omega))

/-- Correctness of `Brockian.isPSmall` below `2209 = 47 ^ 2`. -/
theorem isPSmall_iff {n : ℕ} (hn : n < 2209) : isPSmall n = true ↔ Nat.Prime n := by
  rw [isPSmall_eq_true_iff, Nat.prime_def_le_sqrt]
  have hsq : Nat.sqrt n < 47 := Nat.sqrt_lt'.mpr (by norm_num; omega)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm hms hdvd => ?_⟩
    have hlt : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
    exact h2 m (by omega) hm (by omega) (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m _ hm hmn hmod => ?_⟩
    have hprime : Nat.Prime n := Nat.prime_def_le_sqrt.mpr ⟨h1, h2⟩
    have hdvd : m ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hmod
    rcases hprime.eq_one_or_self_of_dvd m hdvd with h | h <;> omega

/-- The exhaustive Goldbach certificate for all even numbers up to `2 * 947 = 1894`:
each such `n` splits as `p + (n - p)` with both parts prime and with the small prime `p`
taken from the wheel spokes `p < 80`. -/
theorem goldbach_certificate :
    ∀ n < 1895, 4 ≤ n → n % 2 = 0 → ∃ p < 80, isPSmall p ∧ isPSmall (n - p) := by
  decide +kernel

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
Every even natural number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two primes. -/
theorem GoldbachWheelK2_947 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 2 * 947 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  intro n h4 hle hev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨p, hp80, hpP, hqP⟩ := goldbach_certificate n (by omega) h4 (by omega)
  have hpn : p ≤ n := by
    by_contra hcon
    have hzero : n - p = 0 := by omega
    rw [hzero] at hqP
    simp [isPSmall] at hqP
  exact ⟨p, n - p, (isPSmall_iff (by omega)).mp hpP, (isPSmall_iff (by omega)).mp hqP,
    by omega⟩

end Brockian

