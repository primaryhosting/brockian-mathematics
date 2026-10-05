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

lemma solvable_of_two_term (n x w : ℕ) (hx : 0 < x) (hw : 0 < w)
    (h : (4 : ℚ) / n = 1 / x + 1 / w) : ErdosStrausSolvable n := by
  refine ⟨x, w + 1, w * (w + 1), hx, by omega, by positivity, ?_⟩
  have hw' : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hw.ne'
  rw [h]
  push_cast
  field_simp
  ring

/-- For `n ≡ 3 (mod 4)`, writing `n = 4k + 3` we have
`4 / n = 1 / (k + 1) + 1 / (n * (k + 1))`. -/
