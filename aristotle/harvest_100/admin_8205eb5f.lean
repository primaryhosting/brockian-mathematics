/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This module is deliberately import-free (Lean forbids `import` after the header
-- comment above), so primality is spelled out from first principles here.  The
-- companion module `RequestProject.GoldbachWheelK2_1327Mathlib` proves that
-- `Brockian.IsPrimeNat` coincides with Mathlib's `Nat.Prime`, and restates the
-- main theorem in Mathlib's vocabulary.

namespace Brockian

set_option maxRecDepth 100000

/-- Primality, from first principles: `n` is at least `2` and its only divisors are
`1` and `n`. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- Fuel-driven trial division: `trialAux fuel n d` tests that no `e ≥ d` with `e * e ≤ n`
divides `n`, examining at most `fuel` candidates. -/
def trialAux : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, n, d =>
      if n < d * d then true else if n % d = 0 then false else trialAux fuel n (d + 1)

/-- A kernel-friendly primality test. -/
def isPrimeB (n : Nat) : Bool := 2 ≤ n && trialAux n n 2

theorem trialAux_spec :
    ∀ fuel n d, trialAux fuel n d = true →
      ∀ e, d ≤ e → e * e ≤ n → e < d + fuel → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro n d _ e hde _ hlt; omega
  | succ fuel ih =>
      intro n d h e hde hen hlt
      rw [trialAux] at h
      split at h
      · rename_i hdd
        exact absurd hen (by
          have : d * d ≤ e * e := Nat.mul_le_mul hde hde
          omega)
      · split at h
        · exact absurd h (by simp)
        · rename_i hmod
          rcases Nat.eq_or_lt_of_le hde with rfl | hlt'
          · rintro ⟨c, rfl⟩
            exact hmod (Nat.mul_mod_right _ c)
          · exact ih n (d + 1) h e (by omega) hen (by omega)

theorem no_small_divisor {n : Nat} (h : trialAux n n 2 = true) :
    ∀ e, 2 ≤ e → e * e ≤ n → ¬ e ∣ n := by
  intro e he hen
  have hen' : e ≤ n := Nat.le_trans (Nat.le_mul_of_pos_left e (by omega)) hen
  exact trialAux_spec n n 2 h e he hen (by omega)

theorem isPrimeB_spec {n : Nat} (h : isPrimeB n = true) : IsPrimeNat n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hT⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmn : m = n
  · exact Or.inr hmn
  exfalso
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hm2 : 2 ≤ m := by omega
  have hk1 : k ≠ 1 := by rintro rfl; omega
  have hk2 : 2 ≤ k := by omega
  rcases Nat.le_total (m * m) n with hmm | hmm
  · exact no_small_divisor hT m hm2 hmm ⟨k, hk⟩
  · have hkk : k * k ≤ n := by
      have hkm : k ≤ m :=
        Nat.le_of_mul_le_mul_left (by rw [← hk]; exact hmm) (by omega)
      calc k * k ≤ m * k := Nat.mul_le_mul_right k hkm
        _ = n := by omega
    exact no_small_divisor hT k hk2 hkk ⟨m, by rw [hk, Nat.mul_comm]⟩

/-- The wheel of candidate small summands. -/
def wheel : List Nat := List.range 104

/-- Bool-level check that `n` splits as `p + (n - p)` with both parts prime and `p` in the
wheel. -/
def goldbachCheck (n : Nat) : Bool :=
  wheel.any fun p => isPrimeB p && isPrimeB (n - p) && decide (p ≤ n)

theorem goldbachCheck_spec {n : Nat} (h : goldbachCheck n = true) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p ≤ 103 ∧ p + q = n := by
  rw [goldbachCheck, List.any_eq_true] at h
  obtain ⟨p, hp, hcheck⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hpp, hqq⟩, hple⟩ := hcheck
  have hpw : p < 104 := by
    have := List.mem_range.1 (by simpa [wheel] using hp)
    omega
  exact ⟨p, n - p, isPrimeB_spec hpp, isPrimeB_spec hqq, by omega, by omega⟩

/-- The finite verification: every even `n` in `[4, 2654]` passes the wheel check. -/
theorem goldbach_all_check :
    ((List.range 2655).all fun n => !(decide (4 ≤ n ∧ n % 2 = 0)) || goldbachCheck n) = true := by
  decide +kernel

/--
**Goldbach wheel with `K = 2` and wheel modulus `1327`.**

The modulus `1327` is prime, and every even `n` with `4 ≤ n ≤ 2 * 1327` is a sum of two
primes `p + q` in which the wheel summand `p` may always be taken with `p ≤ 103`
(a bound that is attained in this range).
-/
theorem GoldbachWheelK2_1327 :
    IsPrimeNat 1327 ∧
    ∀ n : Nat, 4 ≤ n → n ≤ 2 * 1327 → n % 2 = 0 →
      ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p ≤ 103 ∧ p + q = n := by
  refine ⟨isPrimeB_spec (by decide +kernel), ?_⟩
  intro n h4 hle hev
  have hmem : n ∈ List.range 2655 := List.mem_range.2 (by omega)
  have h := (List.all_eq_true.1 goldbach_all_check) n hmem
  simp only [h4, hev, and_self, decide_true, Bool.not_true, Bool.false_or] at h
  exact goldbachCheck_spec h

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_1327

/-!
# Goldbach Wheel K 2 1327 — Mathlib restatement

`RequestProject.GoldbachWheelK2_1327` is import-free (its mandated header comment must be the
very first thing in the file, and Lean forbids `import` after a module docstring), so it uses
the from-first-principles predicate `Brockian.IsPrimeNat`.  Here we check that this predicate
is exactly `Nat.Prime`, and restate the main theorem in Mathlib's vocabulary.
-/

namespace Brockian

theorem isPrimeNat_iff_prime (n : ℕ) : IsPrimeNat n ↔ Nat.Prime n :=
  Nat.prime_def.symm

/-- Mathlib restatement of `Brockian.GoldbachWheelK2_1327`: the wheel modulus `1327` is prime,
and every even `n` with `4 ≤ n ≤ 2 * 1327` is a sum of two primes whose smaller wheel summand
satisfies `p ≤ 103`. -/
theorem GoldbachWheelK2_1327_prime :
    Nat.Prime 1327 ∧
    ∀ n : ℕ, 4 ≤ n → n ≤ 2 * 1327 → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ 103 ∧ p + q = n := by
  obtain ⟨h1327, hmain⟩ := GoldbachWheelK2_1327
  refine ⟨(isPrimeNat_iff_prime _).1 h1327, ?_⟩
  intro n h4 hle hev
  obtain ⟨p, q, hp, hq, hple, hsum⟩ := hmain n h4 hle (Nat.even_iff.1 hev)
  exact ⟨p, q, (isPrimeNat_iff_prime _).1 hp, (isPrimeNat_iff_prime _).1 hq, hple, hsum⟩

end Brockian

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

