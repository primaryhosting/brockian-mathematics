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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ENNReal
open Set Filter MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Variation of a difference -/

/-- The variation of a difference of two real-valued functions is at most the sum of the
variations. -/

theorem sum_indicator_eq_configCount (x : ℕ → ℝ) (s : Set ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, Set.indicator s (fun _ => (1 : ℝ)) (Int.fract (x n))) =
      (configCount x s N : ℝ) := by
  classical
  rw [configCount]
  simp [Set.indicator_apply, Finset.sum_boole]

/-- **Configuration-count density from bounded variation.**

If a sequence is BV-equidistributed mod 1, then for every subinterval `[a, b) ⊆ [0, 1]` the
density of the indices `n < N` whose fractional part falls in `[a, b)` converges to the
length `b - a`.

The statement is unconditional in the sense that no auxiliary "known result" is assumed as a
hypothesis: the facts that indicators of intervals are of bounded variation and that they
integrate to the length of the interval are proved here. -/
