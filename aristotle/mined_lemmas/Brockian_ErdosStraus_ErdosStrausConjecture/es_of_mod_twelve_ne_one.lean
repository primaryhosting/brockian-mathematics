import Brockian.ErdosStraus

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

/-- `ES n` says that `4 / n` is a sum of three positive unit fractions
(the Erdős–Straus property for `n`; the denominators need not be distinct). -/

theorem es_of_mod_twelve_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 12 ≠ 1) : ES n := by
  by_cases h2 : n % 2 = 0
  · exact es_of_even h2 (by omega)
  by_cases h4 : n % 4 = 3
  · exact es_of_mod_four_eq_three h4
  by_cases h3 : n % 3 = 2
  · exact es_of_mod_three_eq_two h3
  by_cases h3' : n % 3 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    exact es_mul es_three (by omega)
  · omega

/-- Every prime outside the residue class `1 (mod 12)` has the Erdős–Straus property. -/
