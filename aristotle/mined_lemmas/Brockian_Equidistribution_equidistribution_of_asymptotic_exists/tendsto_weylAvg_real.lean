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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

theorem tendsto_weylAvg_real {α : ℝ} (hα : Irrational α) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ =>
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)))
      atTop (𝓝 (∫ x, f x)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hint : (∫ x, F x) = ((∫ x, f x : ℝ) : ℂ) := integral_complex_ofReal
  have havg : ∀ N : ℕ, weylAvg α F N
      = (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          f (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
    intro N
    simp [weylAvg, hF]
  have h := tendsto_weylAvg hα F
  rw [hint] at h
  exact tendsto_ofReal_iff.mp (h.congr havg)

/-! ## Trapezoidal test functions -/

/-- The trapezoidal function which is `1` on `[a + δ, b - δ]`, `0` outside `(a, b)`, and
interpolates linearly in between. -/
