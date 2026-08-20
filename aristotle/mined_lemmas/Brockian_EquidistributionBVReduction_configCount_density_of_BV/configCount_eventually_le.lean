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
# Equidistribution: reduction from continuous test functions to BV (indicator) test functions

This file contains the classical "bounded variation reduction" step in the theory of
equidistribution modulo one: if a sequence `x : ℕ → ℝ` is equidistributed mod `1` in Weyl's
sense (Cesàro averages of *continuous* `1`-periodic test functions converge to the mean of the
test function), then the counting density of the "configurations" `n ↦ Int.fract (x n)` lying in
a subinterval `[a, b) ⊆ [0, 1)` converges to the length `b - a`.

The indicator of an interval is the basic example of a function of bounded variation which is not
continuous, so the content of the main theorem is exactly that the class of admissible test
functions may be enlarged from continuous functions to such BV functions.

The main result is `Brockian.EquidistributionBVReduction.configCount_density_of_BV`; it is
unconditional apart from the (necessary) equidistribution hypothesis on the sequence itself.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma configCount_eventually_le {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (configCount x a b N : ℝ) / N ≤ (b - a) + ε := by
  have h1 := configCount_eventually_ge hx le_rfl ha (le_trans hab hb) (half_pos hε)
  have h2 := configCount_eventually_ge hx (le_trans ha hab) hb le_rfl (half_pos hε)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with N hN1 hN2 hN0
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
  have hpart : (configCount x 0 a N : ℝ) + configCount x a b N + configCount x b 1 N = N := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (configCount_partition x hab N)
  have hdiv : (configCount x 0 a N : ℝ) / N + (configCount x a b N : ℝ) / N
      + (configCount x b 1 N : ℝ) / N = 1 := by
    field_simp
    linarith
  linarith

/-- **Equidistribution implies convergence of configuration densities.**

If `x` is equidistributed modulo one in Weyl's sense (that is, Cesàro averages of continuous
`1`-periodic test functions converge to their mean), then for any subinterval `[a, b) ⊆ [0, 1)`
the density of indices `n < N` with `Int.fract (x n) ∈ [a, b)` tends to `b - a`.

This is the bounded-variation reduction: the (discontinuous, but BV) indicator of an interval is
an admissible test function. -/
