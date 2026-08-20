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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

lemma norm_cesaroAvg_le (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖cesaroAvg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [cesaroAvg, h, norm_nonneg]
  · rw [cesaroAvg, norm_mul, norm_inv]
    have hN : (0 : ℝ) < N := by exact_mod_cast h
    have hsum : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum fun n _ => f.norm_coe_le_norm _
        _ = N * ‖f‖ := by simp
    have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [hcast, inv_mul_le_iff₀ hN]
    linarith

end Basic

/-- The `k`-th Fourier character integrates to zero over the circle for `k ≠ 0`. -/
