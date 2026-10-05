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

lemma solvable_of_pair {n a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : (4 : ℚ) / n = 1 / a + 1 / b) : Solvable n := by
  refine ⟨a, b + 1, b * (b + 1), ha, by positivity, by positivity, ?_⟩
  rw [h, one_div_split b hb]
  ring

/-- If `d ∣ n`, `n > 0` and `4/d` is a sum of three unit fractions, so is `4/n`. -/
