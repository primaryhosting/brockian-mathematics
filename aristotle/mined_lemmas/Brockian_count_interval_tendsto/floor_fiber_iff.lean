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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

lemma floor_fiber_iff {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊(k : ℝ) * y⌋₊ = i ↔ ((i : ℝ) / k ≤ y ∧ y < ((i : ℝ) + 1) / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Nat.floor_eq_iff (by positivity), div_le_iff₀ hk0, lt_div_iff₀ hk0]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> [linarith [h1]; linarith [h2]]
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

