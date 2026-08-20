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
# Weyl's equidistribution criterion, via reduction of BV (indicator) test functions

This file proves the classical **Weyl criterion** (sufficiency direction):
if all nontrivial exponential sums along a real sequence `x : ℕ → ℝ` have vanishing
Cesàro averages, then `x` is equidistributed modulo one in the counting sense.

The proof proceeds by the *BV reduction*: the characteristic function of an interval
(a function of bounded variation) is squeezed between continuous trapezoidal functions
on the circle, and continuous functions on the circle are approximated uniformly by
trigonometric polynomials.

As an application, the sequence `n ↦ n * α` is equidistributed mod one for irrational `α`.
-/

open Filter Topology MeasureTheory Finset

namespace Brockian
namespace EquidistributionBVReduction

noncomputable section

open scoped Classical

instance factOnePos : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circ := AddCircle (1:ℝ)

/-- `x : ℕ → ℝ` is equidistributed modulo one: for every subinterval `[a, b) ⊆ [0,1]`,
the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
`b - a`. -/

lemma avgTendsto_real {x : ℕ → ℝ} (hW : WeylCondition x) {f : Circ → ℝ} (hf : Continuous f) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f ((x n : ℝ) : Circ)) / (N : ℝ))
      atTop (𝓝 (∫ t, f t)) := by
  have hc : AvgTendsto x (fun t => ((f t : ℝ) : ℂ)) :=
    avgTendsto_continuous hW ⟨fun t => ((f t : ℝ) : ℂ), by fun_prop⟩
  rw [AvgTendsto, integral_complex_ofReal] at hc
  refine tendsto_ofReal_iff.mp (hc.congr (fun N => ?_))
  push_cast
  ring

/-! ### Step 3: trapezoidal approximations of indicators -/

/-- A trapezoid supported in `[u, v]`, equal to `1` on `[u + ε, v - ε]`. -/
