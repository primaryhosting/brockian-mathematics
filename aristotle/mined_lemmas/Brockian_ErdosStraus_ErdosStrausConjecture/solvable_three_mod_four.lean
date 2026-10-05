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

lemma solvable_three_mod_four (n : ℕ) (h : n % 4 = 3) : ErdosStrausSolvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine solvable_of_two_term _ (k + 1) ((4 * k + 3) * (k + 1)) (by omega) (by positivity) ?_
  push_cast
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-- For `n ≡ 2 (mod 3)`, writing `n = 3k + 2` we have
`4 / n = 1 / n + 1 / (k + 1) + 1 / (n * (k + 1))`. -/
