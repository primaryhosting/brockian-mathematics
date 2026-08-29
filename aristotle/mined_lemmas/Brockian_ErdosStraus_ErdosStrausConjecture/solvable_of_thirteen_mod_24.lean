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

lemma solvable_of_thirteen_mod_24 {n : ℕ} (hn : n % 24 = 13) : Solvable n := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 24 * t + 13 := ⟨n / 24, by omega⟩
  refine ⟨6 * t + 4, 48 * t ^ 2 + 58 * t + 18,
    2 * (24 * t + 13) * (3 * t + 2) * (24 * t ^ 2 + 29 * t + 9),
    by positivity, by positivity, by positivity, ?_⟩
  have ht : (0:ℚ) ≤ (t:ℚ) := Nat.cast_nonneg t
  have h1 : (24 * (t:ℚ) + 13) ≠ 0 := by positivity
  have h2 : (6 * (t:ℚ) + 4) ≠ 0 := by positivity
  have h3 : (48 * (t:ℚ) ^ 2 + 58 * t + 18) ≠ 0 := by positivity
  have h4 : (3 * (t:ℚ) + 2) ≠ 0 := by positivity
  have h5 : (24 * (t:ℚ) ^ 2 + 29 * t + 9) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The conjecture holds for every `n ≥ 2` with `n % 12 ≠ 1`. -/
