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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Cauchy–Schwarz for the Lebesgue integral on `ℝ`: for continuous, compactly supported
`u, v : ℝ → ℝ` we have `∫ |u| |v| ≤ √(∫ u²) * √(∫ v²)`. -/

lemma integral_abs_mul_le_sqrt_mul_sqrt {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v) :
    (∫ t : ℝ, |u t| * |v t|) ≤ Real.sqrt (∫ t : ℝ, u t ^ 2) * Real.sqrt (∫ t : ℝ, v t ^ 2) := by
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hmu : MemLp (fun t : ℝ => |u t|) (ENNReal.ofReal 2) volume :=
    (hu.abs).memLp_of_hasCompactSupport hsu.abs
  have hmv : MemLp (fun t : ℝ => |v t|) (ENNReal.ofReal 2) volume :=
    (hv.abs).memLp_of_hasCompactSupport hsv.abs
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (f := fun t : ℝ => |u t|) (g := fun t : ℝ => |v t|)
    (Filter.Eventually.of_forall fun t => abs_nonneg _)
    (Filter.Eventually.of_forall fun t => abs_nonneg _) hmu hmv
  have e1 : (∫ t : ℝ, |u t| ^ (2:ℝ)) = ∫ t : ℝ, u t ^ 2 := by
    congr 1; funext t
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have e2 : (∫ t : ℝ, |v t| ^ (2:ℝ)) = ∫ t : ℝ, v t ^ 2 := by
    congr 1; funext t
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e2] at hCS
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hCS

/-- The derivative of a compactly supported differentiable function is compactly supported. -/
