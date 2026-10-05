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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` means that `4 / n` can be written as a sum of three unit fractions
with positive (natural) denominators. -/

theorem solvable_of_mod_twelve_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 12 ≠ 1) : Solvable n := by
  have hn0 : 0 < n := by omega
  by_cases h2 : n % 2 = 0
  · exact solvable_of_even hn0 (Nat.dvd_of_mod_eq_zero h2)
  by_cases h3 : n % 3 = 0
  · exact solvable_of_three_dvd hn0 (Nat.dvd_of_mod_eq_zero h3)
  by_cases h4 : n % 4 = 3
  · exact solvable_of_three_mod_four h4
  exact solvable_of_two_mod_three (by omega)

/-- The conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`. -/
