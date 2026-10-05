/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory

/-- A compactly supported function on `ℝ` vanishes at some point to the left of any given point. -/
theorem exists_le_apply_eq_zero {f : ℝ → ℝ} (hf : HasCompactSupport f) (x : ℝ) :
    ∃ a : ℝ, a ≤ x ∧ f a = 0 := by
  obtain ⟨b, hb⟩ := hf.isCompact.bddBelow
  refine ⟨min x (b - 1), min_le_left _ _, ?_⟩
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have hle : b ≤ min x (b - 1) := hb hmem
  have : min x (b - 1) ≤ b - 1 := min_le_right _ _
  linarith

/-- The one-dimensional base case of the Gagliardo–Nirenberg–Sobolev inequality:
for a compactly supported differentiable function on `ℝ` with integrable derivative,
the supremum norm is bounded by the `L¹` norm of the derivative. -/
theorem sup_le_integral_abs_deriv {u u' : ℝ → ℝ}
    (hderiv : ∀ x : ℝ, HasDerivAt u (u' x) x) (hsupp : HasCompactSupport u)
    (hu' : Integrable u' volume) (x : ℝ) :
    |u x| ≤ ∫ t : ℝ, |u' t| := by
  obtain ⟨a, hax, hua⟩ := exists_le_apply_eq_zero hsupp x
  have hftc : (∫ y : ℝ in a..x, u' y) = u x - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hu'.intervalIntegrable a x)
  rw [hua, sub_zero] at hftc
  calc |u x| = |∫ y : ℝ in a..x, u' y| := by rw [hftc]
    _ ≤ ∫ y : ℝ in a..x, |u' y| := intervalIntegral.abs_integral_le_integral_abs hax
    _ = ∫ y : ℝ in Set.Ioc a x, |u' y| := intervalIntegral.integral_of_le hax
    _ ≤ ∫ t : ℝ, |u' t| :=
        setIntegral_le_integral hu'.abs (Filter.Eventually.of_forall fun t => abs_nonneg _)

/-- **Gagliardo–Nirenberg interpolation inequality** (one-dimensional base case).

For a compactly supported continuously differentiable function `u : ℝ → ℝ`, the `L^∞` norm is
controlled by the geometric mean of the `L²` norms of `u` and of its derivative:
`‖u‖_∞ ^ 2 ≤ 2 ‖u‖_{L²} ‖u'‖_{L²}`. -/
theorem nirenberg_gagliardo {u u' : ℝ → ℝ}
    (hderiv : ∀ x : ℝ, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ^ 2 ≤ 2 * Real.sqrt (∫ t : ℝ, u t ^ 2) * Real.sqrt (∫ t : ℝ, u' t ^ 2) := by
  have hu : Continuous u := by
    refine continuous_iff_continuousAt.2 fun y => (hderiv y).continuousAt
  -- the square of `u`, with its derivative
  set v : ℝ → ℝ := fun t => u t ^ 2 with hv_def
  set v' : ℝ → ℝ := fun t => 2 * u t * u' t with hv'_def
  have hvderiv : ∀ y : ℝ, HasDerivAt v (v' y) y := by
    intro y
    have := (hderiv y).pow 2
    simpa [hv_def, hv'_def, mul_comm, mul_assoc, mul_left_comm] using this
  have hvsupp : HasCompactSupport v := by
    have : HasCompactSupport (u * u) := hsupp.mul_right
    simpa [hv_def, pow_two] using this
  have hv'cont : Continuous v' := by
    exact (continuous_const.mul hu).mul hu'
  have hv'supp : HasCompactSupport v' := by
    have : HasCompactSupport ((fun t : ℝ => 2 * u t) * u') :=
      (hsupp.mul_left (f' := fun _ : ℝ => (2 : ℝ))).mul_right
    simpa [hv'_def, mul_assoc] using this
  have hv'int : Integrable v' volume := hv'cont.integrable_of_hasCompactSupport hv'supp
  -- step 1 : the base case applied to `v = u ^ 2`
  have h1 : |u x| ^ 2 ≤ ∫ t : ℝ, |v' t| := by
    have := sup_le_integral_abs_deriv hvderiv hvsupp hv'int x
    rwa [hv_def, abs_of_nonneg (sq_nonneg _), sq_abs] at this
  -- step 2 : rewrite the right-hand side
  have h2 : (∫ t : ℝ, |v' t|) = 2 * ∫ t : ℝ, |u t| * |u' t| := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [hv'_def, abs_mul, mul_assoc]
  -- step 3 : Cauchy–Schwarz
  have hmem_u : MemLp (fun t : ℝ => |u t|) (ENNReal.ofReal 2) volume := by
    have : MemLp (fun t : ℝ => |u t|) (ENNReal.ofReal 2) volume :=
      (hu.abs).memLp_of_hasCompactSupport (hsupp.abs)
    exact this
  have hmem_u' : MemLp (fun t : ℝ => |u' t|) (ENNReal.ofReal 2) volume := by
    have hsupp' : HasCompactSupport u' := by
      have : HasCompactSupport (deriv u) := hsupp.deriv
      have heq : deriv u = u' := funext fun y => (hderiv y).deriv
      rwa [heq] at this
    exact (hu'.abs).memLp_of_hasCompactSupport hsupp'.abs
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have h3 : (∫ t : ℝ, |u t| * |u' t|) ≤
      (∫ t : ℝ, |u t| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ t : ℝ, |u' t| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg hconj
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hmem_u hmem_u'
  -- step 4 : identify the rpow expressions with square roots
  have hru : (∫ t : ℝ, |u t| ^ (2 : ℝ)) = ∫ t : ℝ, u t ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hru' : (∫ t : ℝ, |u' t| ^ (2 : ℝ)) = ∫ t : ℝ, u' t ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hru, hru', ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h3
  calc |u x| ^ 2 ≤ ∫ t : ℝ, |v' t| := h1
    _ = 2 * ∫ t : ℝ, |u t| * |u' t| := h2
    _ ≤ 2 * (Real.sqrt (∫ t : ℝ, u t ^ 2) * Real.sqrt (∫ t : ℝ, u' t ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 2 * Real.sqrt (∫ t : ℝ, u t ^ 2) * Real.sqrt (∫ t : ℝ, u' t ^ 2) := by ring

end Frontier

