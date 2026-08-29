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

/-!
# Equidistribution from uniform averaging against functions of bounded variation

If a real sequence `x : ℕ → ℝ` has the property that for *every* function `f : ℝ → ℝ` of
bounded variation on `[0,1]` the Cesàro averages `(1/N) ∑_{n < N} f (x n)` converge to
`∫_0^1 f`, then `x` is equidistributed in `[0,1]`: for every subinterval `[a,b) ⊆ [0,1]`
the proportion of indices `n < N` with `x n ∈ [a,b)` converges to `b - a`.

The proof tests the hypothesis on the indicator function of `[a, b)`.  The two facts that
this reduction relies on are proved here rather than assumed, making the statement
unconditional:

* `Brockian.EquidistributionBVReduction.boundedVariationOn_indicator_Ico` : the indicator
  function of an interval `[a, b)` has bounded variation on `[0,1]`;
* `Brockian.EquidistributionBVReduction.intervalIntegral_indicator_Ico` : its integral over
  `[0,1]` equals `b - a` whenever `0 ≤ a ≤ b ≤ 1`.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter Set MeasureTheory
open scoped Topology ENNReal

/-- The Heaviside-type step function `t ↦ 1` if `a ≤ t`, and `0` otherwise. -/

lemma monotone_stepGe (a : ℝ) : Monotone (stepGe a) := by
  intro s t hst
  simp only [stepGe]
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact absurd (h₁.trans hst) h₂
  · norm_num
  · exact le_rfl

/-- Any monotone function has bounded variation on `[0,1]`. -/
