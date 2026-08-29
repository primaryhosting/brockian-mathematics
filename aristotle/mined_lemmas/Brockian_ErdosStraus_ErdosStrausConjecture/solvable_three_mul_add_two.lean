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

/-- `Solvable n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural denominators. -/

theorem solvable_three_mul_add_two (k : ℕ) : Solvable (3 * k + 2) := by
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Unconditional partial result: `4/n` is a sum of three unit fractions for every `n ≥ 2`
which is not congruent to `1` modulo `12`. -/
