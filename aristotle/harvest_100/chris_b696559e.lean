/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- For a `C¹` function with compact support on `ℝ`, the value at any point is bounded by the
total variation `∫ |f'|`. -/
lemma le_integral_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f)
    (x : ℝ) : f x ≤ ∫ t, |deriv f t| := by
  have hderiv_cont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hint : Integrable (deriv f) := hderiv_cont.integrable_of_hasCompactSupport h2f.deriv
  have hint' : Integrable (fun t => |deriv f t|) := hint.abs
  calc f x = ∫ t in Set.Iic x, deriv f t := (h2f.integral_Iic_deriv_eq hf x).symm
    _ ≤ ∫ t in Set.Iic x, |deriv f t| :=
        integral_mono hint.integrableOn hint'.integrableOn fun t => le_abs_self _
    _ ≤ ∫ t, |deriv f t| :=
        setIntegral_le_integral hint' (Filter.Eventually.of_forall fun t => abs_nonneg _)

/-- Cauchy–Schwarz inequality for integrals of continuous compactly supported functions on `ℝ`. -/
lemma integral_abs_mul_abs_le_sqrt_mul_sqrt {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h2f : HasCompactSupport f) (h2g : HasCompactSupport g) :
    ∫ t, |f t| * |g t| ≤ Real.sqrt (∫ t, f t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hmf : MemLp (fun t => |f t|) (ENNReal.ofReal 2) (volume : Measure ℝ) :=
    hf.abs.memLp_of_hasCompactSupport (μ := volume) h2f.abs
  have hmg : MemLp (fun t => |g t|) (ENNReal.ofReal 2) (volume : Measure ℝ) :=
    hg.abs.memLp_of_hasCompactSupport (μ := volume) h2g.abs
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure ℝ)) hpq
    (f := fun t => |f t|) (g := fun t => |g t|)
    (Filter.Eventually.of_forall fun t => abs_nonneg _)
    (Filter.Eventually.of_forall fun t => abs_nonneg _) hmf hmg
  have e : ∀ h : ℝ → ℝ, (∫ t, |h t| ^ (2:ℝ)) = ∫ t, h t ^ 2 := by
    intro h
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |h t| ^ (2:ℝ) = h t ^ 2
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only at key
  rw [e f, e g] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact key

/-- **Gagliardo–Nirenberg interpolation inequality** (base case: dimension `n = 1`,
interpolation parameter `θ = 1/2`).

For a continuously differentiable, compactly supported function `u : ℝ → ℝ` one has the pointwise
bound `|u x| ^ 2 ≤ 2 ‖u‖_{L²} ‖u'‖_{L²}`, i.e. `‖u‖_∞ ≤ √2 · ‖u‖_{L²}^{1/2} · ‖u'‖_{L²}^{1/2}`. -/
theorem nirenberg_gagliardo {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    (x : ℝ) :
    u x ^ 2 ≤ 2 * Real.sqrt (∫ t, u t ^ 2) * Real.sqrt (∫ t, deriv u t ^ 2) := by
  have h1 : ContDiff ℝ 1 (fun t => u t ^ 2) := hu.pow 2
  have h2 : HasCompactSupport (fun t => u t ^ 2) := by
    have := h2u.mul_right (f' := u)
    simpa [sq] using this
  have h3 : ∀ t, deriv (fun t => u t ^ 2) t = 2 * u t * deriv u t := by
    intro t
    have := ((hu.differentiable one_ne_zero t).hasDerivAt).pow 2
    simpa using this.deriv
  have step2 : (∫ t, |deriv (fun t => u t ^ 2) t|) = 2 * ∫ t, |u t| * |deriv u t| := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |deriv (fun t => u t ^ 2) t| = 2 * (|u t| * |deriv u t|)
    rw [h3 t, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have step3 : (∫ t, |u t| * |deriv u t|) ≤
      Real.sqrt (∫ t, u t ^ 2) * Real.sqrt (∫ t, deriv u t ^ 2) :=
    integral_abs_mul_abs_le_sqrt_mul_sqrt hu.continuous (hu.continuous_deriv le_rfl) h2u h2u.deriv
  calc u x ^ 2 ≤ ∫ t, |deriv (fun t => u t ^ 2) t| := le_integral_abs_deriv h1 h2 x
    _ = 2 * ∫ t, |u t| * |deriv u t| := step2
    _ ≤ 2 * (Real.sqrt (∫ t, u t ^ 2) * Real.sqrt (∫ t, deriv u t ^ 2)) := by linarith
    _ = 2 * Real.sqrt (∫ t, u t ^ 2) * Real.sqrt (∫ t, deriv u t ^ 2) := by ring

end Frontier

