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

set_option maxHeartbeats 1000000

namespace Brockian.Equidistribution

open Filter MeasureTheory Set Submodule
open scoped Topology BigOperators

/-- The number of indices `n < N` for which the fractional part of `u n` lies in `[a, b)`. -/

lemma tendsto_circleAvg_fourier {u : ℕ → ℝ} (h : WeylVanishing u) (k : ℤ) :
    Tendsto (circleAvg u (fourier k)) atTop (𝓝 (∫ x : UnitAddCircle, fourier k x)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [integral_fourier_zero]
    have : ∀ N : ℕ, 1 ≤ N → circleAvg u (fourier 0) N = 1 := by
      intro N hN
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp [circleAvg, div_self hN']
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN using (this N hN).symm
  · rw [integral_fourier_ne_zero hk]
    exact (h k hk).congr (fun N => (circleAvg_fourier u k N).symm)

/-- The continuous functions on the circle whose Cesàro averages along `u` converge to their
integral form a submodule. -/
