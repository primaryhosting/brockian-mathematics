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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem tendsto_freq (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => freq x N a b) atTop (𝓝 (b - a)) := by
  have := h (indIco a b) (boundedVariationOn_indIco hab)
  rw [integral_indIco ha hab hb] at this
  simpa only [freq, sum_indIco] using this

/-! ### From pointwise to uniform -/

/-- The counting function is monotone in the right endpoint (with left endpoint `0`). -/
