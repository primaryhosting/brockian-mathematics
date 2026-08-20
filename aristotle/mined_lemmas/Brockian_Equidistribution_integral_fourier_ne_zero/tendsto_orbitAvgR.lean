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
# Weyl's equidistribution theorem for irrational rotations

For an irrational number `a`, the fractional parts `{n * a}` are equidistributed in `[0,1)`:
for every subinterval `[u, v) ⊆ [0,1]` the proportion of `n < N` with `Int.fract (n * a) ∈ [u, v)`
tends to `v - u`.

The proof follows Weyl's method:

* `WeylSumsVanish a` is the statement that all non-trivial exponential (Weyl) sums along the
  orbit have vanishing averages;
* `tendsto_orbitAvg_of_weylSumsVanish` is the *conditional* statement that `WeylSumsVanish a`
  implies convergence of Birkhoff averages of continuous functions to their integral;
* `weylSumsVanish_of_irrational` *discharges* that hypothesis for irrational `a` (geometric
  series estimate), making the result unconditional;
* `equidistribution_of_asymptotic_exists` is the final unconditional interval version.
-/

namespace Brockian.Equidistribution

open Filter Topology MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Birkhoff / empirical average of a complex-valued function over the first `N` points of the
orbit of `0` under the rotation by `a` on the circle `ℝ / ℤ`. -/

theorem tendsto_orbitAvgR {a : ℝ} (ha : Irrational a) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (orbitAvgR a f) atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hcast : ∀ N, orbitAvg a F N = ((orbitAvgR a f N : ℝ) : ℂ) := by
    intro N
    simp only [orbitAvg, orbitAvgR, hF, ContinuousMap.coe_mk]
    push_cast
    ring
  have hint : (∫ x, F x ∂AddCircle.haarAddCircle)
      = ((∫ x, f x ∂AddCircle.haarAddCircle : ℝ) : ℂ) := integral_complex_ofReal
  have h := tendsto_orbitAvg ha F
  rw [hint] at h
  rw [← tendsto_ofReal_iff]
  exact Tendsto.congr hcast h

/-! ### Continuous approximations of indicator functions of intervals -/

/-- A continuous "trapezoid" bump on the circle, supported in the interval `(c, d)`, with
integral at least `d - c - 2 * δ`. -/
