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

theorem fourier_mem_weylGood {α : ℝ} (hα : Irrational α) (k : ℤ) : fourier k ∈ weylGood α := by
  rcases eq_or_ne k 0 with rfl | hk
  · show Tendsto (weylAvg α (fourier 0)) atTop (𝓝 (∫ x : AddCircle (1 : ℝ), (fourier 0) x))
    have hint : (∫ x : AddCircle (1 : ℝ), (fourier (T := (1 : ℝ)) 0) x) = 1 := by
      simp [measureReal_def]
    rw [hint]
    have hval : ∀ N : ℕ, 1 ≤ N → weylAvg α (fourier (T := (1 : ℝ)) 0) N = 1 := by
      intro N hN
      simp only [weylAvg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    exact Tendsto.congr'
      (by filter_upwards [eventually_ge_atTop 1] with N hN using (hval N hN).symm)
      tendsto_const_nhds
  · show Tendsto (weylAvg α (fourier k)) atTop (𝓝 (∫ x : AddCircle (1 : ℝ), (fourier k) x))
    rw [integral_fourier_ne_zero hk]
    exact tendsto_weylAvg_fourier_ne_zero α (exp_ne_one_of_irrational hα hk)

/-- **Weyl's equidistribution theorem, test-function form.** For irrational `α` and any
continuous complex-valued function `f` on the circle `ℝ / ℤ`, the averages of `f` along the
orbit `n ↦ nα` converge to the integral of `f`. -/
