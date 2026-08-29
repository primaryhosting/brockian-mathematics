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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open Filter MeasureTheory AddCircle

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Cesàro average of `f` along the first `N` terms of the sequence `u`. -/

lemma norm_avg_le (u : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) {N : ℕ} (hN : 1 ≤ N) :
    ‖avg u f N‖ ≤ ‖f‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hsum : ‖∑ n ∈ Finset.range N, f (u n)‖ ≤ N * ‖f‖ := by
    calc ‖∑ n ∈ Finset.range N, f (u n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (u n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ :=
          Finset.sum_le_sum fun n _ => f.norm_coe_le_norm (u n)
      _ = N * ‖f‖ := by simp
  have : ‖avg u f N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f (u n)‖ := by
    simp [avg]
  rw [this]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f (u n)‖ ≤ (N : ℝ)⁻¹ * (N * ‖f‖) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖f‖ := by field_simp

