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
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/

theorem andrica_of_le_twentyfour (n : ℕ) (hn : n ≤ 24) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 := by
  interval_cases n
  · exact andrica_of_gap_le_two_mul 0 1 (by norm_num [nthPrime_zero])
      (by norm_num [nthPrime_zero, nthPrime_one])
  · exact andrica_of_gap_le_two_mul 1 1 (by norm_num [nthPrime_one])
      (by norm_num [nthPrime_one, nthPrime_two])
  · exact andrica_of_gap_le_two_mul 2 2 (by norm_num [nthPrime_two])
      (by norm_num [nthPrime_two, nthPrime_three])
  · exact andrica_of_gap_le_two_mul 3 2 (by norm_num [nthPrime_three])
      (by norm_num [nthPrime_three, nthPrime_four])
  · exact andrica_of_gap_le_two_mul 4 3 (by norm_num [nthPrime_four])
      (by norm_num [nthPrime_four, nthPrime_5])
  · exact andrica_of_gap_le_two_mul 5 3 (by norm_num [nthPrime_5])
      (by norm_num [nthPrime_5, nthPrime_6])
  · exact andrica_of_gap_le_two_mul 6 4 (by norm_num [nthPrime_6])
      (by norm_num [nthPrime_6, nthPrime_7])
  · exact andrica_of_gap_le_two_mul 7 4 (by norm_num [nthPrime_7])
      (by norm_num [nthPrime_7, nthPrime_8])
  · exact andrica_of_gap_le_two_mul 8 4 (by norm_num [nthPrime_8])
      (by norm_num [nthPrime_8, nthPrime_9])
  · exact andrica_of_gap_le_two_mul 9 5 (by norm_num [nthPrime_9])
      (by norm_num [nthPrime_9, nthPrime_10])
  · exact andrica_of_gap_le_two_mul 10 5 (by norm_num [nthPrime_10])
      (by norm_num [nthPrime_10, nthPrime_11])
  · exact andrica_of_gap_le_two_mul 11 6 (by norm_num [nthPrime_11])
      (by norm_num [nthPrime_11, nthPrime_12])
  · exact andrica_of_gap_le_two_mul 12 6 (by norm_num [nthPrime_12])
      (by norm_num [nthPrime_12, nthPrime_13])
  · exact andrica_of_gap_le_two_mul 13 6 (by norm_num [nthPrime_13])
      (by norm_num [nthPrime_13, nthPrime_14])
  · exact andrica_of_gap_le_two_mul 14 6 (by norm_num [nthPrime_14])
      (by norm_num [nthPrime_14, nthPrime_15])
  · exact andrica_of_gap_le_two_mul 15 7 (by norm_num [nthPrime_15])
      (by norm_num [nthPrime_15, nthPrime_16])
  · exact andrica_of_gap_le_two_mul 16 7 (by norm_num [nthPrime_16])
      (by norm_num [nthPrime_16, nthPrime_17])
  · exact andrica_of_gap_le_two_mul 17 7 (by norm_num [nthPrime_17])
      (by norm_num [nthPrime_17, nthPrime_18])
  · exact andrica_of_gap_le_two_mul 18 8 (by norm_num [nthPrime_18])
      (by norm_num [nthPrime_18, nthPrime_19])
  · exact andrica_of_gap_le_two_mul 19 8 (by norm_num [nthPrime_19])
      (by norm_num [nthPrime_19, nthPrime_20])
  · exact andrica_of_gap_le_two_mul 20 8 (by norm_num [nthPrime_20])
      (by norm_num [nthPrime_20, nthPrime_21])
  · exact andrica_of_gap_le_two_mul 21 8 (by norm_num [nthPrime_21])
      (by norm_num [nthPrime_21, nthPrime_22])
  · exact andrica_of_gap_le_two_mul 22 9 (by norm_num [nthPrime_22])
      (by norm_num [nthPrime_22, nthPrime_23])
  · exact andrica_of_gap_le_two_mul 23 9 (by norm_num [nthPrime_23])
      (by norm_num [nthPrime_23, nthPrime_24])
  · exact andrica_of_gap_le_two_mul 24 9 (by norm_num [nthPrime_24])
      (by norm_num [nthPrime_24, nthPrime_25])

/-! ## Oppermann implies Andrica -/

