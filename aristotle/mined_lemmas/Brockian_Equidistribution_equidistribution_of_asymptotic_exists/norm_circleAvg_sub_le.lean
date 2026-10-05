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

lemma norm_circleAvg_sub_le (u : ℕ → ℝ) (f g : C(UnitAddCircle, ℂ)) {N : ℕ} (hN : 1 ≤ N) :
    ‖circleAvg u f N - circleAvg u g N‖ ≤ ‖f - g‖ := by
  have hrw : circleAvg u f N - circleAvg u g N
      = (∑ n ∈ Finset.range N, (f - g) (u n : UnitAddCircle)) / N := by
    simp [circleAvg, ContinuousMap.sub_apply, Finset.sum_sub_distrib, sub_div]
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  rw [hrw, norm_div]
  have h1 : ‖∑ n ∈ Finset.range N, (f - g) (u n : UnitAddCircle)‖ ≤ N * ‖f - g‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ n ∈ Finset.range N, ‖(f - g) (u n : UnitAddCircle)‖
        ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ :=
          Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm _ _
      _ = N * ‖f - g‖ := by simp
  have h2 : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [h2, div_le_iff₀ hNpos]
  calc ‖∑ n ∈ Finset.range N, (f - g) (u n : UnitAddCircle)‖ ≤ N * ‖f - g‖ := h1
    _ = ‖f - g‖ * N := by ring

