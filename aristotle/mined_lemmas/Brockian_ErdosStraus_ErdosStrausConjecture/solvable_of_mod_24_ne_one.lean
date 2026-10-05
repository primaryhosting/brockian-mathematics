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

namespace Brockian.ErdosStraus

/-- `ErdosStrausSolvable n` says that `4 / n` is a sum of three unit fractions with
positive natural denominators. -/

theorem solvable_of_mod_24_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 24 ≠ 1) :
    ErdosStrausSolvable n := by
  have hn0 : 0 < n := by omega
  have key : n % 2 = 0 ∨ n % 3 = 0 ∨ n % 4 = 3 ∨ n % 3 = 2 ∨ n % 8 = 5 := by omega
  rcases key with h' | h' | h' | h' | h'
  · exact solvable_of_even hn0 h'
  · exact solvable_of_three_dvd hn0 h'
  · exact solvable_of_mod_four_eq_three h'
  · exact solvable_of_mod_three_eq_two h'
  · exact solvable_of_mod_eight_eq_five h'

/-- **Reduction to primes.** The full Erdős–Straus conjecture is equivalent to its restriction
to primes congruent to `1` modulo `24`. -/
