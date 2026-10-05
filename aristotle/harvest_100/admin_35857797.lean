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

import Mathlib

/-!
# The Gilbreath triangle: definition and explicit values

Auxiliary file for `Brockian.GilbreathConjecture`.  It sets up the Gilbreath triangle of the
primes and records the explicit values of its first eleven rows (as far as they are
determined by the first `45` primes).
-/

namespace Brockian.GilbreathConjecture

/-- Row `n`, entry `k` of the Gilbreath triangle of the prime numbers:
row `0` is the sequence of primes, and each later row consists of the absolute values of the
differences of consecutive entries of the previous row. -/
noncomputable def gilbreath : ℕ → ℕ → ℕ
  | 0, k => Nat.nth Nat.Prime k
  | n + 1, k => ((gilbreath n (k + 1) : ℤ) - (gilbreath n k : ℤ)).natAbs

@[simp] theorem gilbreath_zero (k : ℕ) : gilbreath 0 k = Nat.nth Nat.Prime k := rfl

theorem gilbreath_succ (n k : ℕ) :
    gilbreath (n + 1) k = ((gilbreath n (k + 1) : ℤ) - (gilbreath n k : ℤ)).natAbs := rfl

theorem nth_prime_eq_of_count {n p : ℕ} (hp : p.Prime) (h : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p := by
  subst h; exact Nat.nth_count hp

set_option maxRecDepth 100000

/-! ### The first 45 primes -/

@[simp] theorem nth_prime_00 : Nat.nth Nat.Prime 0 = 2 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_01 : Nat.nth Nat.Prime 1 = 3 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_02 : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_03 : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_04 : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_05 : Nat.nth Nat.Prime 5 = 13 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_06 : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_07 : Nat.nth Nat.Prime 7 = 19 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_08 : Nat.nth Nat.Prime 8 = 23 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_09 : Nat.nth Nat.Prime 9 = 29 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_10 : Nat.nth Nat.Prime 10 = 31 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_11 : Nat.nth Nat.Prime 11 = 37 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_12 : Nat.nth Nat.Prime 12 = 41 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_13 : Nat.nth Nat.Prime 13 = 43 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_14 : Nat.nth Nat.Prime 14 = 47 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_15 : Nat.nth Nat.Prime 15 = 53 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_16 : Nat.nth Nat.Prime 16 = 59 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_17 : Nat.nth Nat.Prime 17 = 61 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_18 : Nat.nth Nat.Prime 18 = 67 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_19 : Nat.nth Nat.Prime 19 = 71 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_20 : Nat.nth Nat.Prime 20 = 73 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_21 : Nat.nth Nat.Prime 21 = 79 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_22 : Nat.nth Nat.Prime 22 = 83 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_23 : Nat.nth Nat.Prime 23 = 89 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_24 : Nat.nth Nat.Prime 24 = 97 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_25 : Nat.nth Nat.Prime 25 = 101 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_26 : Nat.nth Nat.Prime 26 = 103 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_27 : Nat.nth Nat.Prime 27 = 107 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_28 : Nat.nth Nat.Prime 28 = 109 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_29 : Nat.nth Nat.Prime 29 = 113 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_30 : Nat.nth Nat.Prime 30 = 127 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_31 : Nat.nth Nat.Prime 31 = 131 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_32 : Nat.nth Nat.Prime 32 = 137 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_33 : Nat.nth Nat.Prime 33 = 139 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_34 : Nat.nth Nat.Prime 34 = 149 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_35 : Nat.nth Nat.Prime 35 = 151 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_36 : Nat.nth Nat.Prime 36 = 157 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_37 : Nat.nth Nat.Prime 37 = 163 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_38 : Nat.nth Nat.Prime 38 = 167 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_39 : Nat.nth Nat.Prime 39 = 173 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_40 : Nat.nth Nat.Prime 40 = 179 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_41 : Nat.nth Nat.Prime 41 = 181 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_42 : Nat.nth Nat.Prime 42 = 191 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_43 : Nat.nth Nat.Prime 43 = 193 :=
  nth_prime_eq_of_count (by norm_num) (by decide)
@[simp] theorem nth_prime_44 : Nat.nth Nat.Prime 44 = 197 :=
  nth_prime_eq_of_count (by norm_num) (by decide)

/-! ### Row 1 -/

@[simp] theorem gilbreath_1_00 : gilbreath 1 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_01 : gilbreath 1 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_02 : gilbreath 1 2 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_03 : gilbreath 1 3 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_04 : gilbreath 1 4 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_05 : gilbreath 1 5 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_06 : gilbreath 1 6 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_07 : gilbreath 1 7 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_08 : gilbreath 1 8 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_09 : gilbreath 1 9 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_10 : gilbreath 1 10 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_11 : gilbreath 1 11 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_12 : gilbreath 1 12 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_13 : gilbreath 1 13 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_14 : gilbreath 1 14 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_15 : gilbreath 1 15 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_16 : gilbreath 1 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_17 : gilbreath 1 17 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_18 : gilbreath 1 18 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_19 : gilbreath 1 19 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_20 : gilbreath 1 20 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_21 : gilbreath 1 21 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_22 : gilbreath 1 22 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_23 : gilbreath 1 23 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_24 : gilbreath 1 24 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_25 : gilbreath 1 25 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_26 : gilbreath 1 26 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_27 : gilbreath 1 27 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_28 : gilbreath 1 28 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_29 : gilbreath 1 29 = 14 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_30 : gilbreath 1 30 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_31 : gilbreath 1 31 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_32 : gilbreath 1 32 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_33 : gilbreath 1 33 = 10 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_34 : gilbreath 1 34 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_35 : gilbreath 1 35 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_36 : gilbreath 1 36 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_37 : gilbreath 1 37 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_38 : gilbreath 1 38 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_39 : gilbreath 1 39 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_40 : gilbreath 1 40 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_41 : gilbreath 1 41 = 10 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_42 : gilbreath 1 42 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_1_43 : gilbreath 1 43 = 4 := by simp [gilbreath_succ]

/-! ### Row 2 -/

@[simp] theorem gilbreath_2_00 : gilbreath 2 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_01 : gilbreath 2 1 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_02 : gilbreath 2 2 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_03 : gilbreath 2 3 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_04 : gilbreath 2 4 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_05 : gilbreath 2 5 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_06 : gilbreath 2 6 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_07 : gilbreath 2 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_08 : gilbreath 2 8 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_09 : gilbreath 2 9 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_10 : gilbreath 2 10 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_11 : gilbreath 2 11 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_12 : gilbreath 2 12 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_13 : gilbreath 2 13 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_14 : gilbreath 2 14 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_15 : gilbreath 2 15 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_16 : gilbreath 2 16 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_17 : gilbreath 2 17 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_18 : gilbreath 2 18 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_19 : gilbreath 2 19 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_20 : gilbreath 2 20 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_21 : gilbreath 2 21 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_22 : gilbreath 2 22 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_23 : gilbreath 2 23 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_24 : gilbreath 2 24 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_25 : gilbreath 2 25 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_26 : gilbreath 2 26 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_27 : gilbreath 2 27 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_28 : gilbreath 2 28 = 10 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_29 : gilbreath 2 29 = 10 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_30 : gilbreath 2 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_31 : gilbreath 2 31 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_32 : gilbreath 2 32 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_33 : gilbreath 2 33 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_34 : gilbreath 2 34 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_35 : gilbreath 2 35 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_36 : gilbreath 2 36 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_37 : gilbreath 2 37 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_38 : gilbreath 2 38 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_39 : gilbreath 2 39 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_40 : gilbreath 2 40 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_41 : gilbreath 2 41 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_2_42 : gilbreath 2 42 = 2 := by simp [gilbreath_succ]

/-! ### Row 3 -/

@[simp] theorem gilbreath_3_00 : gilbreath 3 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_01 : gilbreath 3 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_02 : gilbreath 3 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_03 : gilbreath 3 3 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_04 : gilbreath 3 4 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_05 : gilbreath 3 5 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_06 : gilbreath 3 6 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_07 : gilbreath 3 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_08 : gilbreath 3 8 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_09 : gilbreath 3 9 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_10 : gilbreath 3 10 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_11 : gilbreath 3 11 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_12 : gilbreath 3 12 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_13 : gilbreath 3 13 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_14 : gilbreath 3 14 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_15 : gilbreath 3 15 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_16 : gilbreath 3 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_17 : gilbreath 3 17 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_18 : gilbreath 3 18 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_19 : gilbreath 3 19 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_20 : gilbreath 3 20 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_21 : gilbreath 3 21 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_22 : gilbreath 3 22 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_23 : gilbreath 3 23 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_24 : gilbreath 3 24 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_25 : gilbreath 3 25 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_26 : gilbreath 3 26 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_27 : gilbreath 3 27 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_28 : gilbreath 3 28 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_29 : gilbreath 3 29 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_30 : gilbreath 3 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_31 : gilbreath 3 31 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_32 : gilbreath 3 32 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_33 : gilbreath 3 33 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_34 : gilbreath 3 34 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_35 : gilbreath 3 35 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_36 : gilbreath 3 36 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_37 : gilbreath 3 37 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_38 : gilbreath 3 38 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_39 : gilbreath 3 39 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_40 : gilbreath 3 40 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_3_41 : gilbreath 3 41 = 6 := by simp [gilbreath_succ]

/-! ### Row 4 -/

@[simp] theorem gilbreath_4_00 : gilbreath 4 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_01 : gilbreath 4 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_02 : gilbreath 4 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_03 : gilbreath 4 3 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_04 : gilbreath 4 4 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_05 : gilbreath 4 5 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_06 : gilbreath 4 6 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_07 : gilbreath 4 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_08 : gilbreath 4 8 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_09 : gilbreath 4 9 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_10 : gilbreath 4 10 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_11 : gilbreath 4 11 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_12 : gilbreath 4 12 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_13 : gilbreath 4 13 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_14 : gilbreath 4 14 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_15 : gilbreath 4 15 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_16 : gilbreath 4 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_17 : gilbreath 4 17 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_18 : gilbreath 4 18 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_19 : gilbreath 4 19 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_20 : gilbreath 4 20 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_21 : gilbreath 4 21 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_22 : gilbreath 4 22 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_23 : gilbreath 4 23 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_24 : gilbreath 4 24 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_25 : gilbreath 4 25 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_26 : gilbreath 4 26 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_27 : gilbreath 4 27 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_28 : gilbreath 4 28 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_29 : gilbreath 4 29 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_30 : gilbreath 4 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_31 : gilbreath 4 31 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_32 : gilbreath 4 32 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_33 : gilbreath 4 33 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_34 : gilbreath 4 34 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_35 : gilbreath 4 35 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_36 : gilbreath 4 36 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_37 : gilbreath 4 37 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_38 : gilbreath 4 38 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_39 : gilbreath 4 39 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_4_40 : gilbreath 4 40 = 6 := by simp [gilbreath_succ]

/-! ### Row 5 -/

@[simp] theorem gilbreath_5_00 : gilbreath 5 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_01 : gilbreath 5 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_02 : gilbreath 5 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_03 : gilbreath 5 3 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_04 : gilbreath 5 4 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_05 : gilbreath 5 5 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_06 : gilbreath 5 6 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_07 : gilbreath 5 7 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_08 : gilbreath 5 8 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_09 : gilbreath 5 9 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_10 : gilbreath 5 10 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_11 : gilbreath 5 11 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_12 : gilbreath 5 12 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_13 : gilbreath 5 13 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_14 : gilbreath 5 14 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_15 : gilbreath 5 15 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_16 : gilbreath 5 16 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_17 : gilbreath 5 17 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_18 : gilbreath 5 18 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_19 : gilbreath 5 19 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_20 : gilbreath 5 20 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_21 : gilbreath 5 21 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_22 : gilbreath 5 22 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_23 : gilbreath 5 23 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_24 : gilbreath 5 24 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_25 : gilbreath 5 25 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_26 : gilbreath 5 26 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_27 : gilbreath 5 27 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_28 : gilbreath 5 28 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_29 : gilbreath 5 29 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_30 : gilbreath 5 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_31 : gilbreath 5 31 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_32 : gilbreath 5 32 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_33 : gilbreath 5 33 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_34 : gilbreath 5 34 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_35 : gilbreath 5 35 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_36 : gilbreath 5 36 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_37 : gilbreath 5 37 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_38 : gilbreath 5 38 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_5_39 : gilbreath 5 39 = 2 := by simp [gilbreath_succ]

/-! ### Row 6 -/

@[simp] theorem gilbreath_6_00 : gilbreath 6 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_01 : gilbreath 6 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_02 : gilbreath 6 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_03 : gilbreath 6 3 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_04 : gilbreath 6 4 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_05 : gilbreath 6 5 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_06 : gilbreath 6 6 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_07 : gilbreath 6 7 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_08 : gilbreath 6 8 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_09 : gilbreath 6 9 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_10 : gilbreath 6 10 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_11 : gilbreath 6 11 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_12 : gilbreath 6 12 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_13 : gilbreath 6 13 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_14 : gilbreath 6 14 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_15 : gilbreath 6 15 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_16 : gilbreath 6 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_17 : gilbreath 6 17 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_18 : gilbreath 6 18 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_19 : gilbreath 6 19 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_20 : gilbreath 6 20 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_21 : gilbreath 6 21 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_22 : gilbreath 6 22 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_23 : gilbreath 6 23 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_24 : gilbreath 6 24 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_25 : gilbreath 6 25 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_26 : gilbreath 6 26 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_27 : gilbreath 6 27 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_28 : gilbreath 6 28 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_29 : gilbreath 6 29 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_30 : gilbreath 6 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_31 : gilbreath 6 31 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_32 : gilbreath 6 32 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_33 : gilbreath 6 33 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_34 : gilbreath 6 34 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_35 : gilbreath 6 35 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_36 : gilbreath 6 36 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_37 : gilbreath 6 37 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_6_38 : gilbreath 6 38 = 2 := by simp [gilbreath_succ]

/-! ### Row 7 -/

@[simp] theorem gilbreath_7_00 : gilbreath 7 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_01 : gilbreath 7 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_02 : gilbreath 7 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_03 : gilbreath 7 3 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_04 : gilbreath 7 4 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_05 : gilbreath 7 5 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_06 : gilbreath 7 6 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_07 : gilbreath 7 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_08 : gilbreath 7 8 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_09 : gilbreath 7 9 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_10 : gilbreath 7 10 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_11 : gilbreath 7 11 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_12 : gilbreath 7 12 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_13 : gilbreath 7 13 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_14 : gilbreath 7 14 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_15 : gilbreath 7 15 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_16 : gilbreath 7 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_17 : gilbreath 7 17 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_18 : gilbreath 7 18 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_19 : gilbreath 7 19 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_20 : gilbreath 7 20 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_21 : gilbreath 7 21 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_22 : gilbreath 7 22 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_23 : gilbreath 7 23 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_24 : gilbreath 7 24 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_25 : gilbreath 7 25 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_26 : gilbreath 7 26 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_27 : gilbreath 7 27 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_28 : gilbreath 7 28 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_29 : gilbreath 7 29 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_30 : gilbreath 7 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_31 : gilbreath 7 31 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_32 : gilbreath 7 32 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_33 : gilbreath 7 33 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_34 : gilbreath 7 34 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_35 : gilbreath 7 35 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_36 : gilbreath 7 36 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_7_37 : gilbreath 7 37 = 0 := by simp [gilbreath_succ]

/-! ### Row 8 -/

@[simp] theorem gilbreath_8_00 : gilbreath 8 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_01 : gilbreath 8 1 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_02 : gilbreath 8 2 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_03 : gilbreath 8 3 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_04 : gilbreath 8 4 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_05 : gilbreath 8 5 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_06 : gilbreath 8 6 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_07 : gilbreath 8 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_08 : gilbreath 8 8 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_09 : gilbreath 8 9 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_10 : gilbreath 8 10 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_11 : gilbreath 8 11 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_12 : gilbreath 8 12 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_13 : gilbreath 8 13 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_14 : gilbreath 8 14 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_15 : gilbreath 8 15 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_16 : gilbreath 8 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_17 : gilbreath 8 17 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_18 : gilbreath 8 18 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_19 : gilbreath 8 19 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_20 : gilbreath 8 20 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_21 : gilbreath 8 21 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_22 : gilbreath 8 22 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_23 : gilbreath 8 23 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_24 : gilbreath 8 24 = 8 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_25 : gilbreath 8 25 = 6 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_26 : gilbreath 8 26 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_27 : gilbreath 8 27 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_28 : gilbreath 8 28 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_29 : gilbreath 8 29 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_30 : gilbreath 8 30 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_31 : gilbreath 8 31 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_32 : gilbreath 8 32 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_33 : gilbreath 8 33 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_34 : gilbreath 8 34 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_35 : gilbreath 8 35 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_8_36 : gilbreath 8 36 = 0 := by simp [gilbreath_succ]

/-! ### Row 9 -/

@[simp] theorem gilbreath_9_00 : gilbreath 9 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_01 : gilbreath 9 1 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_02 : gilbreath 9 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_03 : gilbreath 9 3 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_04 : gilbreath 9 4 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_05 : gilbreath 9 5 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_06 : gilbreath 9 6 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_07 : gilbreath 9 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_08 : gilbreath 9 8 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_09 : gilbreath 9 9 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_10 : gilbreath 9 10 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_11 : gilbreath 9 11 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_12 : gilbreath 9 12 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_13 : gilbreath 9 13 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_14 : gilbreath 9 14 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_15 : gilbreath 9 15 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_16 : gilbreath 9 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_17 : gilbreath 9 17 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_18 : gilbreath 9 18 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_19 : gilbreath 9 19 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_20 : gilbreath 9 20 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_21 : gilbreath 9 21 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_22 : gilbreath 9 22 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_23 : gilbreath 9 23 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_24 : gilbreath 9 24 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_25 : gilbreath 9 25 = 4 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_26 : gilbreath 9 26 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_27 : gilbreath 9 27 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_28 : gilbreath 9 28 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_29 : gilbreath 9 29 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_30 : gilbreath 9 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_31 : gilbreath 9 31 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_32 : gilbreath 9 32 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_33 : gilbreath 9 33 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_34 : gilbreath 9 34 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_9_35 : gilbreath 9 35 = 2 := by simp [gilbreath_succ]

/-! ### Row 10 -/

@[simp] theorem gilbreath_10_00 : gilbreath 10 0 = 1 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_01 : gilbreath 10 1 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_02 : gilbreath 10 2 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_03 : gilbreath 10 3 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_04 : gilbreath 10 4 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_05 : gilbreath 10 5 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_06 : gilbreath 10 6 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_07 : gilbreath 10 7 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_08 : gilbreath 10 8 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_09 : gilbreath 10 9 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_10 : gilbreath 10 10 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_11 : gilbreath 10 11 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_12 : gilbreath 10 12 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_13 : gilbreath 10 13 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_14 : gilbreath 10 14 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_15 : gilbreath 10 15 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_16 : gilbreath 10 16 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_17 : gilbreath 10 17 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_18 : gilbreath 10 18 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_19 : gilbreath 10 19 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_20 : gilbreath 10 20 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_21 : gilbreath 10 21 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_22 : gilbreath 10 22 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_23 : gilbreath 10 23 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_24 : gilbreath 10 24 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_25 : gilbreath 10 25 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_26 : gilbreath 10 26 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_27 : gilbreath 10 27 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_28 : gilbreath 10 28 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_29 : gilbreath 10 29 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_30 : gilbreath 10 30 = 2 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_31 : gilbreath 10 31 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_32 : gilbreath 10 32 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_33 : gilbreath 10 33 = 0 := by simp [gilbreath_succ]
@[simp] theorem gilbreath_10_34 : gilbreath 10 34 = 2 := by simp [gilbreath_succ]

end Brockian.GilbreathConjecture

import Brockian.GilbreathTriangle

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Gilbreath triangle of the primes is defined in `Brockian.GilbreathTriangle`:
row `0` is the sequence of primes `2, 3, 5, 7, 11, …` and

`gilbreath (n+1) k = |gilbreath n (k+1) - gilbreath n k|`.

Gilbreath's conjecture asserts that every row after row `0` begins with `1`.  It is an open
problem.  This file contains:

* the statement `GilbreathConjecture`;
* an unconditional parity invariant: for `n ≥ 1` the leading entry of row `n` is odd (hence
  nonzero) and all its other entries are even;
* Odlyzko's criterion, a conditional reduction: if a row starts with `1` followed by `m`
  entries in `{0, 2}`, then the next `m` rows also start with `1`; consequently the
  conjecture follows from the existence of arbitrarily far reaching such rows;
* an unconditional verification of the conjecture for all rows `1 ≤ n ≤ 44`.
-/

namespace Brockian.GilbreathConjecture

/-- **Gilbreath's conjecture**: every row of the Gilbreath triangle of the primes after
row `0` starts with the value `1`. -/
def GilbreathConjecture : Prop := ∀ n : ℕ, gilbreath (n + 1) 0 = 1

/-! ## A parity invariant (unconditional)

Every row after the zeroth one has an odd first entry and even later entries.  In particular
the entry whose value Gilbreath's conjecture predicts is never `0` and never even.
-/

private theorem natAbs_sub_mod_two (a b : ℕ) : ((a : ℤ) - b).natAbs % 2 = (a + b) % 2 := by
  omega

theorem odd_nth_prime {k : ℕ} (hk : 1 ≤ k) : Odd (Nat.nth Nat.Prime k) := by
  have h3 : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime k :=
    Nat.nth_monotone Nat.infinite_setOf_prime hk
  have h1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_01
  exact (Nat.prime_nth_prime k).odd_of_ne_two (by omega)

/-- Row `n + 1` of the Gilbreath triangle has an odd first entry and even remaining entries. -/
theorem gilbreath_parity (n : ℕ) :
    Odd (gilbreath (n + 1) 0) ∧ ∀ k, 1 ≤ k → Even (gilbreath (n + 1) k) := by
  induction n with
  | zero =>
    refine ⟨by rw [gilbreath_1_00]; decide, ?_⟩
    intro k hk
    have h1 : Odd (Nat.nth Nat.Prime k) := odd_nth_prime hk
    have h2 : Odd (Nat.nth Nat.Prime (k + 1)) := odd_nth_prime (by omega)
    rw [Nat.even_iff, gilbreath_succ, gilbreath_zero, gilbreath_zero, natAbs_sub_mod_two]
    rw [Nat.odd_iff] at h1 h2
    omega
  | succ n ih =>
    obtain ⟨h0, hk⟩ := ih
    rw [Nat.odd_iff] at h0
    have h1 := hk (0 + 1) (by omega)
    rw [Nat.even_iff] at h1
    refine ⟨?_, ?_⟩
    · rw [Nat.odd_iff, gilbreath_succ, natAbs_sub_mod_two]
      omega
    · intro k hkk
      have ha := hk k hkk
      have hb := hk (k + 1) (by omega)
      rw [Nat.even_iff] at ha hb ⊢
      rw [gilbreath_succ, natAbs_sub_mod_two]
      omega

/-- The first entry of any row after row `0` is odd. -/
theorem gilbreath_head_odd (n : ℕ) : Odd (gilbreath (n + 1) 0) := (gilbreath_parity n).1

/-- All entries after the first one of any row after row `0` are even. -/
theorem gilbreath_tail_even {n k : ℕ} (hk : 1 ≤ k) : Even (gilbreath (n + 1) k) :=
  (gilbreath_parity n).2 k hk

/-- The first entry of any row after row `0` is nonzero. -/
theorem gilbreath_head_ne_zero (n : ℕ) : gilbreath (n + 1) 0 ≠ 0 := by
  have := gilbreath_head_odd n
  rw [Nat.odd_iff] at this
  omega

/-! ## Odlyzko's criterion (conditional reduction)

If a row starts with `1` and its next `m` entries all lie in `{0, 2}`, then the same is true
of the next row with `m - 1` in place of `m`.  Consequently the next `m` rows all start
with `1`, and Gilbreath's conjecture reduces to finding, for every `N`, such a row `n ≤ N`
whose run of `{0,2}`-entries is long enough to reach `N`.
-/

/-- `RowGood n m` says that row `n` starts with `1` and its entries at positions
`1, …, m` all belong to `{0, 2}`. -/
def RowGood (n m : ℕ) : Prop :=
  gilbreath n 0 = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → gilbreath n k = 0 ∨ gilbreath n k = 2

theorem RowGood.mono {n m m' : ℕ} (h : RowGood n m) (hm : m' ≤ m) : RowGood n m' :=
  ⟨h.1, fun k hk hkm => h.2 k hk (hkm.trans hm)⟩

/-- One step of Odlyzko's argument. -/
theorem RowGood.step {n m : ℕ} (h : RowGood n (m + 1)) : RowGood (n + 1) m := by
  obtain ⟨h0, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have := h2 (0 + 1) (by omega) (by omega)
    rw [gilbreath_succ, h0]
    omega
  · intro k hk hkm
    have ha := h2 (k + 1) (by omega) (by omega)
    have hb := h2 k hk (by omega)
    rw [gilbreath_succ]
    omega

/-- Iterating Odlyzko's step: the property propagates down the triangle, losing one
position of the guaranteed run at each row. -/
theorem RowGood.iterate {n m : ℕ} (h : RowGood n m) : ∀ j, j ≤ m → RowGood (n + j) (m - j) := by
  intro j
  induction j generalizing n m with
  | zero =>
    intro _
    simpa using h
  | succ j ih =>
    intro hj
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have := ih h.step (by omega)
    rw [show n + (j + 1) = (n + 1) + j by omega, show m + 1 - (j + 1) = m - j by omega]
    exact this

/-- If row `n` starts with `1` followed by `m` entries in `{0,2}`, then each of the rows
`n, n+1, …, n+m` starts with `1`. -/
theorem RowGood.head {n m j : ℕ} (h : RowGood n m) (hj : j ≤ m) : gilbreath (n + j) 0 = 1 :=
  (h.iterate j hj).1

/-- **Conditional reduction (Odlyzko's criterion).**  If for every `N` there is a row
`n ≤ N` which starts with `1` and whose following `m ≥ N - n` entries all lie in `{0, 2}`,
then Gilbreath's conjecture holds. -/
theorem gilbreathConjecture_of_rowGood
    (H : ∀ N : ℕ, ∃ n m : ℕ, n ≤ N ∧ N ≤ n + m ∧ RowGood n m) :
    GilbreathConjecture := by
  intro N
  obtain ⟨n, m, h1, h2, hg⟩ := H (N + 1)
  have := hg.head (j := N + 1 - n) (by omega)
  rwa [show n + (N + 1 - n) = N + 1 by omega] at this

/-! ## An unconditional verification of the first rows

Row `10` of the triangle is `1, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 2, 0, 0, …`; its first `34`
entries after the leading `1` all lie in `{0, 2}`, so Odlyzko's criterion certifies rows
`10` through `44`.  Rows `1` through `9` are checked directly.
-/

theorem gilbreath_rowGood_ten : RowGood 10 34 := by
  refine ⟨gilbreath_10_00, ?_⟩
  intro k hk hkm
  interval_cases k <;> simp

/-- Gilbreath's conjecture holds for all rows `1 ≤ n ≤ 44`. -/
theorem gilbreath_head_eq_one_of_le_44 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 44) :
    gilbreath n 0 = 1 := by
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> simp
  · have := gilbreath_rowGood_ten.head (j := n - 10) (by omega)
    rwa [show 10 + (n - 10) = n by omega] at this

end Brockian.GilbreathConjecture

