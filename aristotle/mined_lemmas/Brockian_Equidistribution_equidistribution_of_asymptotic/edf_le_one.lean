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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Filter Topology

namespace Brockian.Equidistribution

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` is `< c`. -/

lemma edf_le_one (x : ℕ → ℝ) (N : ℕ) (c : ℝ) : edf x N c ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [edf, hN]
  · rw [edf, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast countLT_le x N c

