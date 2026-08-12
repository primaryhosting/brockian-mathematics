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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian.AndricaConjecture

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

@[simp] lemma nthPrime_0 : nthPrime 0 = 2 := Nat.nth_prime_zero_eq_two
@[simp] lemma nthPrime_1 : nthPrime 1 = 3 := Nat.nth_prime_one_eq_three
@[simp] lemma nthPrime_2 : nthPrime 2 = 5 := Nat.nth_prime_two_eq_five
@[simp] lemma nthPrime_3 : nthPrime 3 = 7 := Nat.nth_prime_three_eq_seven
@[simp] lemma nthPrime_4 : nthPrime 4 = 11 := Nat.nth_prime_four_eq_eleven

/-- If `m` is prime and there are exactly `k` primes below `m`, then `m` is the `k`-th prime. -/
lemma nthPrime_eq_of_count {k m : ℕ} (hp : Nat.Prime m) (hc : Nat.count Nat.Prime m = k) :
    nthPrime k = m := by
  subst hc; exact Nat.nth_count hp

@[simp] lemma nthPrime_5 : nthPrime 5 = 13 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_6 : nthPrime 6 = 17 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_7 : nthPrime 7 = 19 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_8 : nthPrime 8 = 23 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_9 : nthPrime 9 = 29 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_10 : nthPrime 10 = 31 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_11 : nthPrime 11 = 37 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_12 : nthPrime 12 = 41 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_13 : nthPrime 13 = 43 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_14 : nthPrime 14 = 47 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_15 : nthPrime 15 = 53 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_16 : nthPrime 16 = 59 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_17 : nthPrime 17 = 61 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_18 : nthPrime 18 = 67 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_19 : nthPrime 19 = 71 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_20 : nthPrime 20 = 73 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_21 : nthPrime 21 = 79 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_22 : nthPrime 22 = 83 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_23 : nthPrime 23 = 89 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_24 : nthPrime 24 = 97 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_25 : nthPrime 25 = 101 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_26 : nthPrime 26 = 103 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_27 : nthPrime 27 = 107 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_28 : nthPrime 28 = 109 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_29 : nthPrime 29 = 113 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_30 : nthPrime 30 = 127 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_31 : nthPrime 31 = 131 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_32 : nthPrime 32 = 137 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_33 : nthPrime 33 = 139 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_34 : nthPrime 34 = 149 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_35 : nthPrime 35 = 151 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_36 : nthPrime 36 = 157 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_37 : nthPrime 37 = 163 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_38 : nthPrime 38 = 167 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_39 : nthPrime 39 = 173 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_40 : nthPrime 40 = 179 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_41 : nthPrime 41 = 181 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_42 : nthPrime 42 = 191 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_43 : nthPrime 43 = 193 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_44 : nthPrime 44 = 197 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_45 : nthPrime 45 = 199 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_46 : nthPrime 46 = 211 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_47 : nthPrime 47 = 223 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_48 : nthPrime 48 = 227 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_49 : nthPrime 49 = 229 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_50 : nthPrime 50 = 233 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_51 : nthPrime 51 = 239 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_52 : nthPrime 52 = 241 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_53 : nthPrime 53 = 251 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_54 : nthPrime 54 = 257 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_55 : nthPrime 55 = 263 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_56 : nthPrime 56 = 269 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_57 : nthPrime 57 = 271 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_58 : nthPrime 58 = 277 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_59 : nthPrime 59 = 281 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_60 : nthPrime 60 = 283 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_61 : nthPrime 61 = 293 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_62 : nthPrime 62 = 307 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_63 : nthPrime 63 = 311 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_64 : nthPrime 64 = 313 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_65 : nthPrime 65 = 317 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_66 : nthPrime 66 = 331 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_67 : nthPrime 67 = 337 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_68 : nthPrime 68 = 347 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_69 : nthPrime 69 = 349 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_70 : nthPrime 70 = 353 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_71 : nthPrime 71 = 359 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_72 : nthPrime 72 = 367 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_73 : nthPrime 73 = 373 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_74 : nthPrime 74 = 379 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_75 : nthPrime 75 = 383 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_76 : nthPrime 76 = 389 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_77 : nthPrime 77 = 397 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_78 : nthPrime 78 = 401 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_79 : nthPrime 79 = 409 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_80 : nthPrime 80 = 419 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_81 : nthPrime 81 = 421 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_82 : nthPrime 82 = 431 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_83 : nthPrime 83 = 433 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_84 : nthPrime 84 = 439 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_85 : nthPrime 85 = 443 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_86 : nthPrime 86 = 449 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_87 : nthPrime 87 = 457 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_88 : nthPrime 88 = 461 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_89 : nthPrime 89 = 463 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_90 : nthPrime 90 = 467 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_91 : nthPrime 91 = 479 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_92 : nthPrime 92 = 487 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_93 : nthPrime 93 = 491 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_94 : nthPrime 94 = 499 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_95 : nthPrime 95 = 503 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_96 : nthPrime 96 = 509 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_97 : nthPrime 97 = 521 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_98 : nthPrime 98 = 523 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_99 : nthPrime 99 = 541 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

@[simp] lemma nthPrime_100 : nthPrime 100 = 547 :=
  nthPrime_eq_of_count (by norm_num) (by norm_num [Nat.count_succ])

lemma prime_nthPrime (n : ℕ) : Nat.Prime (nthPrime n) := Nat.prime_nth_prime n

lemma nthPrime_pos (n : ℕ) : 0 < nthPrime n := (prime_nthPrime n).pos

lemma two_le_nthPrime (n : ℕ) : 2 ≤ nthPrime n := (prime_nthPrime n).two_le

lemma nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (Nat.lt_succ_self n)

/-- The elementary reformulation of the Andrica inequality:
`(p_{n+1} - p_n - 1)^2 < 4 * p_n`, an inequality between natural numbers
(subtraction being truncated subtraction).  This form is decidable for each
individual `n`. -/
def AndricaGapBound : Prop :=
  ∀ n : ℕ, (nthPrime (n + 1) - nthPrime n - 1) ^ 2 < 4 * nthPrime n

/-- The Andrica inequality at index `n`: `√p_{n+1} - √p_n < 1`. -/
def AndricaAt (n : ℕ) : Prop :=
  Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1

/-! ### A real-analytic lemma -/

/-- For nonnegative reals, `√y - √x < 1` is equivalent to `y < x + 2√x + 1`. -/
lemma sqrt_sub_sqrt_lt_one_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt y - Real.sqrt x < 1 ↔ y < x + 2 * Real.sqrt x + 1 := by
  rw [sub_lt_iff_lt_add, show (1 : ℝ) + Real.sqrt x = Real.sqrt x + 1 by ring,
    show x + 2 * Real.sqrt x + 1 = (Real.sqrt x + 1) ^ 2 by
      rw [add_sq, Real.sq_sqrt hx]; ring]
  constructor
  · intro h
    calc y = (Real.sqrt y) ^ 2 := (Real.sq_sqrt hy).symm
      _ < _ := by nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  · intro h
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hy, Real.sqrt_nonneg y]

/-! ### Equivalence between the analytic and the arithmetic form -/

/-- Pointwise equivalence between the Andrica inequality and its arithmetic form. -/
lemma andricaAt_iff (n : ℕ) :
    AndricaAt n ↔ (nthPrime (n + 1) - nthPrime n - 1) ^ 2 < 4 * nthPrime n := by
  set a := nthPrime n with ha
  set b := nthPrime (n + 1) with hb
  have hapos : 0 < a := nthPrime_pos n
  have hareal : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hsqrt_pos : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr hareal
  have hsq : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt hareal.le
  rw [AndricaAt, ← ha, ← hb, sqrt_sub_sqrt_lt_one_iff (by positivity) (by positivity)]
  rcases le_or_gt b (a + 1) with h | h
  · -- degenerate case: the arithmetic inequality is `0 < 4a`, and the analytic one holds too
    have h0 : b - a - 1 = 0 := by omega
    rw [h0]
    have hb' : (b : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast h
    constructor
    · intro _; simpa using hapos
    · intro _; nlinarith
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + k + 1 := ⟨b - a - 1, by omega⟩
    have hkb : b - a - 1 = k := by omega
    rw [hkb]
    have hbr : (b : ℝ) = (a : ℝ) + (k : ℝ) + 1 := by rw [hk]; push_cast; ring
    rw [hbr]
    constructor
    · intro h1
      have hk2 : (k : ℝ) ^ 2 < 4 * (a : ℝ) := by nlinarith
      exact_mod_cast hk2
    · intro h1
      have hk2 : (k : ℝ) ^ 2 < 4 * (a : ℝ) := by exact_mod_cast h1
      nlinarith

/-- The Andrica conjecture is *equivalent* to the purely arithmetic statement
`(p_{n+1} - p_n - 1)^2 < 4 * p_n` for all `n`. -/
theorem andrica_iff_gapBound :
    AndricaGapBound ↔ ∀ n : ℕ, AndricaAt n :=
  ⟨fun h n => (andricaAt_iff n).mpr (h n), fun h n => (andricaAt_iff n).mp (h n)⟩

/-! ### The conditional Andrica conjecture

The Andrica conjecture is open, so what is proved here is the reduction of the
conjecture to the arithmetic gap bound `AndricaGapBound`, together with the
unconditional verification of small cases below. -/

/-- **Andrica's conjecture** (conditional on the arithmetic gap bound
`AndricaGapBound`, which is equivalent to it by `andrica_iff_gapBound`):
for every `n`, `√p_{n+1} - √p_n < 1`. -/
theorem AndricaConjecture (h : AndricaGapBound) (n : ℕ) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 :=
  (andricaAt_iff n).mpr (h n)

/-- A sufficient condition in terms of prime gaps: if `p_{n+1} - p_n ≤ 2 √p_n`
(in the integer form `(p_{n+1} - p_n)^2 ≤ 4 p_n`), then Andrica's inequality holds at `n`. -/
theorem andricaAt_of_gap_sq_le (n : ℕ)
    (h : (nthPrime (n + 1) - nthPrime n) ^ 2 ≤ 4 * nthPrime n) : AndricaAt n := by
  refine (andricaAt_iff n).mpr (lt_of_lt_of_le ?_ h)
  have hlt : nthPrime n < nthPrime (n + 1) := nthPrime_lt_nthPrime_succ n
  have h1 : nthPrime (n + 1) - nthPrime n - 1 < nthPrime (n + 1) - nthPrime n := by omega
  exact Nat.pow_lt_pow_left h1 (by norm_num)

/-! ### Unconditional verification of small cases -/

/-- Unconditional verification of Andrica's inequality for the first 101 primes:
`√p_{n+1} - √p_n < 1` for all `n ≤ 99` (i.e. up to `p_100 = 547`). -/
theorem andricaAt_of_le_ninetyNine {n : ℕ} (hn : n ≤ 99) : AndricaAt n := by
  interval_cases n <;> exact andricaAt_of_gap_sq_le _ (by norm_num)

end Brockian.AndricaConjecture

