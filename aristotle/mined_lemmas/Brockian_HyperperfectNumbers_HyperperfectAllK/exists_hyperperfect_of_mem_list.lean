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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/

theorem exists_hyperperfect_of_mem_list :
    ∀ k ∈ ({1, 2, 3, 4, 6, 10, 11, 12, 18, 19, 30, 31, 35, 48, 59, 60} : Finset ℕ),
      ∃ n, Hyperperfect k n := by
  intro k hk
  fin_cases hk
  · exact wit (p := 2) (a := 1) (q := 3) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 3) (a := 1) (q := 7) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 5) (a := 2) (q := 13) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)
  · exact wit (p := 5) (a := 4) (q := 3121) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 7) (a := 1) (q := 43) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 11) (a := 2) (q := 1321) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 17) (a := 2) (q := 37) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 17) (a := 1) (q := 41) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 31) (a := 1) (q := 43) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 29) (a := 2) (q := 61) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 47) (a := 1) (q := 83) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 47) (a := 2) (q := 97) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 53) (a := 2) (q := 109) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 53) (a := 1) (q := 509) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 89) (a := 2) (q := 181) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 73) (a := 1) (q := 337) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)

/-! ### The conjecture -/

/-- The statement "for every `k ≥ 1` there is a `k`-hyperperfect number". -/
