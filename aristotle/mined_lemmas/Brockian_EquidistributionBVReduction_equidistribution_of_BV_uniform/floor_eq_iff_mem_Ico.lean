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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

lemma floor_eq_iff_mem_Ico {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊(K : ℝ) * y⌋₊ = i ↔ y ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(div_le_iff₀ hKpos).2 (by linarith [h1]), (lt_div_iff₀ hKpos).2 (by linarith [h2])⟩
  · rintro ⟨h1, h2⟩
    have h1' := (div_le_iff₀ hKpos).1 h1
    have h2' := (lt_div_iff₀ hKpos).1 h2
    constructor <;> nlinarith

/-- The fibers of `n ↦ ⌊K * fract (x n)⌋₊` decompose a sum over `range N` into sums over the
subintervals `[i/K, (i+1)/K)`. -/
