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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` states that `4 / n` can be written as a sum of three
unit fractions with positive integer denominators. -/

theorem solvable_of_ne_one_mod_twelve (n : ℕ) (hn : 2 ≤ n) (h : n % 12 ≠ 1) :
    ErdosStrausSolvable n := by
  have hn0 : 0 < n := by omega
  rcases Nat.eq_zero_or_pos (n % 2) with h2 | h2
  · exact solvable_of_dvd hn0 (Nat.dvd_of_mod_eq_zero h2) solvable_two
  rcases Nat.eq_zero_or_pos (n % 3) with h3 | h3
  · exact solvable_of_dvd hn0 (Nat.dvd_of_mod_eq_zero h3) solvable_three
  · have hcase : n % 4 = 3 ∨ n % 3 = 2 := by omega
    rcases hcase with h4 | h4
    · exact solvable_three_mod_four n h4
    · exact solvable_two_mod_three n h4

/-- The Erdős–Straus conjecture, reduced to its hard prime case: if `4 / p` is a sum of
three unit fractions for every prime `p ≡ 1 (mod 12)`, then `4 / n` is a sum of three
unit fractions for every `n ≥ 2`.

The reduction itself is proved unconditionally here; the hypothesis isolates exactly the
open part of the conjecture. -/
