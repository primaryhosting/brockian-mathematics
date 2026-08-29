import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Cauchy–Schwarz (Hölder with exponents `2, 2`) for continuous, compactly supported
functions on the line. -/
theorem integral_abs_mul_abs_le_sqrt_mul_sqrt (f g : ℝ → ℝ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    ∫ t, |f t| * |g t| ≤ Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hconj
    (f := fun t => |f t|) (g := fun t => |g t|)
    (Filter.Eventually.of_forall (fun t => abs_nonneg _))
    (Filter.Eventually.of_forall (fun t => abs_nonneg _))
    ((hf.abs).memLp_of_hasCompactSupport (hfs.abs))
    ((hg.abs).memLp_of_hasCompactSupport (hgs.abs))
  have e1 : ∀ x : ℝ, |x| ^ (2:ℝ) = x ^ 2 := by
    intro x
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp_rw [e1] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert h using 3

/-- The fundamental theorem of calculus step: the square of a `C¹` compactly supported
function is bounded by the total variation of its square. -/
theorem sq_le_integral_two_mul_abs_mul_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    f x ^ 2 ≤ ∫ t, 2 * (|f t| * |deriv f t|) := by
  have hcont : Continuous f := hf.continuous
  have hderiv : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgderiv : ∀ t : ℝ, deriv (fun s => f s ^ 2) t = 2 * f t * deriv f t := by
    intro t
    have h1 : HasDerivAt f (deriv f t) t := (hdiff t).hasDerivAt
    have h2 : HasDerivAt (fun s => f s ^ 2) (2 * f t * deriv f t) t := by
      have h3 := h1.pow 2
      simpa [mul_comm, mul_assoc] using h3
    exact h2.deriv
  obtain ⟨b, hb⟩ : BddBelow (tsupport f) := hsupp.isCompact.bddBelow
  set a : ℝ := min x b - 1 with ha
  have hax : a ≤ x := by simp [ha]
  have hfa : f a = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hb hmem
    have h2 : a ≤ b - 1 := by simp [ha]
    linarith
  have hcontderiv : Continuous (fun t => deriv (fun s => f s ^ 2) t) := by
    simp only [hgderiv]
    exact (continuous_const.mul hcont).mul hderiv
  have hFTC : ∫ y in a..x, deriv (fun s => f s ^ 2) y = f x ^ 2 - f a ^ 2 :=
    intervalIntegral.integral_deriv_eq_sub (fun y _ => (hdiff y).pow 2)
      (hcontderiv.intervalIntegrable _ _)
  have habs : ∀ y : ℝ, |deriv (fun s => f s ^ 2) y| = 2 * (|f y| * |deriv f y|) := by
    intro y
    rw [hgderiv, abs_mul, abs_mul]
    norm_num [mul_assoc]
  have hint : Integrable (fun t => 2 * (|f t| * |deriv f t|)) volume :=
    (continuous_const.mul ((hcont.abs).mul (hderiv.abs))).integrable_of_hasCompactSupport
      (((hsupp.abs).mul_right).mul_left)
  have hnn : 0 ≤ᵐ[volume] fun t => 2 * (|f t| * |deriv f t|) :=
    Filter.Eventually.of_forall (fun t => by positivity)
  calc f x ^ 2 = ∫ y in a..x, deriv (fun s => f s ^ 2) y := by rw [hFTC, hfa]; ring
    _ ≤ |∫ y in a..x, deriv (fun s => f s ^ 2) y| := le_abs_self _
    _ ≤ ∫ y in a..x, |deriv (fun s => f s ^ 2) y| :=
        intervalIntegral.abs_integral_le_integral_abs hax
    _ = ∫ y in Set.Ioc a x, 2 * (|f y| * |deriv f y|) := by
        rw [intervalIntegral.integral_of_le hax]; simp_rw [habs]
    _ ≤ ∫ y, 2 * (|f y| * |deriv f y|) := setIntegral_le_integral hint hnn

/-- **Gagliardo–Nirenberg interpolation inequality** (one-dimensional base case,
also known as the Ladyzhenskaya-type estimate):
for a continuously differentiable, compactly supported function `f : ℝ → ℝ`,
`‖f‖_∞ ^ 2 ≤ 2 ‖f‖_{L²} ‖f'‖_{L²}`. -/
theorem nirenberg_gagliardo {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    f x ^ 2 ≤ 2 * (Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, deriv f t ^ 2)) := by
  have hcont : Continuous f := hf.continuous
  have hderiv : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hcs := integral_abs_mul_abs_le_sqrt_mul_sqrt f (deriv f) hcont hsupp hderiv hsupp.deriv
  have hint : Integrable (fun t => |f t| * |deriv f t|) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hcont.abs).mul (hderiv.abs)
    · exact (hsupp.abs).mul_right
  have h1 : (∫ t, 2 * (|f t| * |deriv f t|)) = 2 * ∫ t, |f t| * |deriv f t| := by
    rw [integral_const_mul]
  have h2 := sq_le_integral_two_mul_abs_mul_abs_deriv hf hsupp x
  rw [h1] at h2
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_left hcs (by norm_num)

end Frontier

