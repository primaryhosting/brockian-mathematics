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

theorem weylAvg_sub_le (α : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖weylAvg α f N - weylAvg α g N‖ ≤ ‖f - g‖ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [weylAvg]
  have h1 : weylAvg α f N - weylAvg α g N
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [weylAvg, ContinuousMap.sub_apply, Finset.sum_sub_distrib]
    ring
  rw [h1, norm_mul, norm_inv, Complex.norm_natCast]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : ‖∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖
      ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖
        ≤ ∑ n ∈ Finset.range N, ‖(f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ :=
          Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm _ _
      _ = N * ‖f - g‖ := by simp
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, (f - g) (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ))‖
      ≤ (N : ℝ)⁻¹ * (N * ‖f - g‖) := by gcongr
    _ = ‖f - g‖ := by field_simp

