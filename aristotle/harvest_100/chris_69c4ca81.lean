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
lemma hasCompactSupport_of_hasDerivAt {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hsupp : HasCompactSupport f) : HasCompactSupport f' := by
  have hfd : f' = deriv f := funext fun t => ((hderiv t).deriv).symm
  rw [hfd]
  exact hsupp.deriv

/-- Below the (compact) support of `f`, the function vanishes: there is `a ≤ x` with `f a = 0`. -/
lemma exists_le_eq_zero_of_hasCompactSupport {f : ℝ → ℝ} (hsupp : HasCompactSupport f) (x : ℝ) :
    ∃ a : ℝ, a ≤ x ∧ f a = 0 := by
  obtain ⟨R, hR⟩ := (hsupp.isCompact.isBounded).subset_closedBall (0:ℝ)
  refine ⟨min x (-R - 1) - 1, by have := min_le_left x (-R - 1); linarith, ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := min_le_right x (-R - 1)
  have h3 : -(min x (-R - 1) - 1) ≤ |min x (-R - 1) - 1| := neg_le_abs _
  linarith

/-- **Gagliardo–Nirenberg interpolation inequality**, one-dimensional base case
(`p = ∞`, `q = r = 2`, interpolation parameter `θ = 1/2`).

If `f : ℝ → ℝ` is continuously differentiable with derivative `f'` and has compact support, then
`‖f‖_∞ ≤ √2 · ‖f‖_{L²}^{1/2} · ‖f'‖_{L²}^{1/2}`, stated here in the equivalent squared, pointwise
form `f x ^ 2 ≤ 2 · (∫ f²)^{1/2} · (∫ (f')²)^{1/2}`. -/
theorem nirenberg_gagliardo {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'c : Continuous f') (hsupp : HasCompactSupport f) (x : ℝ) :
    f x ^ 2 ≤ 2 * Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, f' t ^ 2) := by
  have hf : Continuous f := continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
  have hsupp' : HasCompactSupport f' := hasCompactSupport_of_hasDerivAt hderiv hsupp
  obtain ⟨a, hax, hfa⟩ := exists_le_eq_zero_of_hasCompactSupport hsupp x
  have hcont2 : Continuous fun t : ℝ => 2 * f t * f' t := by fun_prop
  have hcontabs : Continuous fun t : ℝ => 2 * (|f t| * |f' t|) := by fun_prop
  have hsuppabs : HasCompactSupport fun t : ℝ => 2 * (|f t| * |f' t|) := by
    apply HasCompactSupport.mul_left
    exact (hsupp.abs).mul_right
  have key : (∫ t in a..x, 2 * f t * f' t) = f x ^ 2 - f a ^ 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => f t ^ 2)
      (fun t _ => ?_) (hcont2.intervalIntegrable _ _)
    simpa [mul_comm] using (hderiv t).pow 2
  have h1 : (∫ t in a..x, 2 * f t * f' t) ≤ ∫ t in a..x, 2 * (|f t| * |f' t|) := by
    refine intervalIntegral.integral_mono_on hax (hcont2.intervalIntegrable _ _)
      (hcontabs.intervalIntegrable _ _) (fun t _ => ?_)
    rw [mul_assoc]
    have : f t * f' t ≤ |f t| * |f' t| := by
      calc f t * f' t ≤ |f t * f' t| := le_abs_self _
        _ = |f t| * |f' t| := abs_mul _ _
    linarith
  have h2 : (∫ t in a..x, 2 * (|f t| * |f' t|)) ≤ ∫ t : ℝ, 2 * (|f t| * |f' t|) := by
    rw [intervalIntegral.integral_of_le hax]
    refine setIntegral_le_integral (hcontabs.integrable_of_hasCompactSupport hsuppabs) ?_
    filter_upwards with t
    positivity
  have h3 : (∫ t : ℝ, 2 * (|f t| * |f' t|)) = 2 * ∫ t : ℝ, |f t| * |f' t| := by
    rw [integral_const_mul]
  have h4 : (∫ t : ℝ, |f t| * |f' t|)
      ≤ Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, f' t ^ 2) :=
    integral_abs_mul_le_sqrt_mul_sqrt hf hf'c hsupp hsupp'
  have hfa2 : f a ^ 2 = 0 := by rw [hfa]; ring
  nlinarith [h1, h2, h3, h4, key, hfa2]

/-- **Gagliardo–Nirenberg interpolation inequality**, one-dimensional base case, in the usual
multiplicative form: for a compactly supported, continuously differentiable `f : ℝ → ℝ`,
`‖f‖_∞ ≤ √2 · ‖f‖_{L²}^{1/2} · ‖f'‖_{L²}^{1/2}`. -/
theorem nirenberg_gagliardo_sup {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'c : Continuous f') (hsupp : HasCompactSupport f) (x : ℝ) :
    |f x| ≤ Real.sqrt 2 * (∫ t : ℝ, f t ^ 2) ^ ((1:ℝ)/4) * (∫ t : ℝ, f' t ^ 2) ^ ((1:ℝ)/4) := by
  set A := ∫ t : ℝ, f t ^ 2 with hAdef
  set B := ∫ t : ℝ, f' t ^ 2 with hBdef
  have hA : 0 ≤ A := integral_nonneg fun t => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun t => sq_nonneg _
  have h := nirenberg_gagliardo hderiv hf'c hsupp x
  have h1 : |f x| = Real.sqrt (f x ^ 2) := (Real.sqrt_sq_eq_abs (f x)).symm
  have h2 : Real.sqrt (f x ^ 2) ≤ Real.sqrt (2 * Real.sqrt A * Real.sqrt B) := Real.sqrt_le_sqrt h
  have h3 : Real.sqrt (2 * Real.sqrt A * Real.sqrt B)
      = Real.sqrt 2 * Real.sqrt (Real.sqrt A) * Real.sqrt (Real.sqrt B) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt (Real.sqrt A) = A ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hA]
    norm_num
  have h5 : Real.sqrt (Real.sqrt B) = B ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hB]
    norm_num
  rw [h1, ← h4, ← h5]
  exact h2.trans_eq h3

end Frontier

