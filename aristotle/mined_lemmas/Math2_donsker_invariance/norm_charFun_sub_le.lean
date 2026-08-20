/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Donsker.Defs
import RequestProject.Donsker.CharFun
import RequestProject.Donsker.CLT
import RequestProject.Donsker.Tight
import RequestProject.Donsker.Levy

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

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Math2

/-- **Donsker's invariance principle** (convergence of the finite-dimensional distributions).

Let `μ` be the law of a centered step with unit variance, let `S_m` be the associated random walk
with i.i.d. steps (the steps being the coordinates of `ℕ → ℝ` under the product measure
`Math2.iidLaw μ`), and let `W_n(u) = S_{⌊n u⌋} / √n` be the rescaled walk.

Then, for any finite set of times `t 0 ≤ t 1 ≤ … ≤ t (k-1)`, the law `Math2.walkLaw μ t k n` of
the random vector `(W_n(t 0), …, W_n(t (k-1)))` converges weakly, as `n → ∞`, to the law
`Math2.bmLaw t k` of `(B_{t 0}, …, B_{t (k-1)})`, where `B` is a Brownian motion.  Weak
convergence is expressed as convergence of the integrals of all bounded continuous functions.

The limit does not depend on the step distribution `μ` (only on its mean and variance): this is
the invariance in Donsker's invariance principle.  That `Math2.bmLaw t k` really is the
finite-dimensional distribution of Brownian motion is the content of
`Math2.charFun_bmLaw_eq`: it is the centered Gaussian law with covariance
`min (t i) (t j)`. -/

lemma norm_charFun_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (s : ℝ) :
    ‖charFun μ s - (1 - (s : ℂ) ^ 2 / 2)‖ ≤ s ^ 2 * taylorErr μ |s| := by
  have hfun : ∀ x : ℝ, (1 - (s * x) ^ 2 / 2 : ℝ) = 1 - s ^ 2 / 2 * x ^ 2 := fun x ↦ by ring
  have hint1 : Integrable (fun x : ℝ ↦ x) μ := by
    have h2 : Integrable (fun x : ℝ ↦ 1 + x ^ 2) μ := (integrable_const (1 : ℝ)).add hint
    refine Integrable.mono h2 (by fun_prop) ?_
    filter_upwards with x
    have h3 : ‖(1 : ℝ) + x ^ 2‖ = 1 + x ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h3, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  have hIexp : Integrable (fun x : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * I)) μ := by
    refine Integrable.mono (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  have h0 : Integrable (fun x : ℝ ↦ (1 : ℝ) - s ^ 2 / 2 * x ^ 2) μ :=
    (integrable_const (1 : ℝ)).sub (hint.const_mul (s ^ 2 / 2))
  have hIa : Integrable (fun x : ℝ ↦ ((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ)) μ := by
    simp only [hfun]
    exact h0.ofReal
  have hIb : Integrable (fun x : ℝ ↦ ((s * x : ℝ) : ℂ) * I) μ :=
    ((hint1.const_mul s).ofReal).mul_const I
  have hIab : Integrable
      (fun x : ℝ ↦ ((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ) + ((s * x : ℝ) : ℂ) * I) μ := hIa.add hIb
  have e1 : ∫ x : ℝ, (((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ) + ((s * x : ℝ) : ℂ) * I) ∂μ
      = 1 - (s : ℂ) ^ 2 / 2 := by
    rw [integral_add hIa hIb, integral_complex_ofReal, integral_mul_const,
      integral_complex_ofReal]
    have ha : ∫ x : ℝ, (1 - (s * x) ^ 2 / 2 : ℝ) ∂μ = 1 - s ^ 2 / 2 := by
      simp only [hfun]
      rw [integral_sub (integrable_const 1) (hint.const_mul (s ^ 2 / 2)), integral_const_mul, hvar]
      simp
    have hb : ∫ x : ℝ, (s * x : ℝ) ∂μ = 0 := by rw [integral_const_mul, hmean, mul_zero]
    rw [ha, hb]
    push_cast
    ring
  have hsplit : ∀ x : ℝ, (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)
      = ((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ) + ((s * x : ℝ) : ℂ) * I := by
    intro x; push_cast; ring
  have hIfull : Integrable (fun x : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * I)
      - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)) μ := by
    simp only [hsplit]
    exact hIexp.sub hIab
  have key : charFun μ s - (1 - (s : ℂ) ^ 2 / 2)
      = ∫ x : ℝ, (Complex.exp (((s * x : ℝ) : ℂ) * I)
          - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)) ∂μ := by
    simp only [hsplit]
    rw [integral_sub hIexp hIab, e1, charFun_apply_real]
    congr 1
    exact congrArg _ (funext fun x ↦ by push_cast; ring_nf)
  rw [key]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ x : ℝ, ‖Complex.exp (((s * x : ℝ) : ℂ) * I)
      - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ s ^ 2 * min (|s| * |x| ^ 3) (4 * x ^ 2) := by
    intro x
    refine (norm_exp_mul_I_sub_taylor_le (s * x)).trans ?_
    have h1 : |s * x| ^ 3 = s ^ 2 * (|s| * |x| ^ 3) := by
      rw [abs_mul, mul_pow, show |s| ^ 3 = |s| ^ 2 * |s| by ring, sq_abs]
      ring
    have h2 : 4 * (s * x) ^ 2 = s ^ 2 * (4 * x ^ 2) := by ring
    rw [h1, h2, ← mul_min_of_nonneg _ _ (sq_nonneg s)]
  have hmin_int : Integrable (fun x : ℝ ↦ min (|s| * |x| ^ 3) (4 * x ^ 2)) μ :=
    integrable_taylorErr_integrand μ hint (abs_nonneg s)
  have hnorm_int : Integrable (fun x : ℝ ↦ ‖Complex.exp (((s * x : ℝ) : ℂ) * I)
      - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)‖) μ :=
    hIfull.norm
  calc ∫ x : ℝ, ‖Complex.exp (((s * x : ℝ) : ℂ) * I)
        - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)‖ ∂μ
      ≤ ∫ x : ℝ, s ^ 2 * min (|s| * |x| ^ 3) (4 * x ^ 2) ∂μ :=
        integral_mono hnorm_int (hmin_int.const_mul _) hbound
    _ = s ^ 2 * taylorErr μ |s| := by rw [integral_const_mul]; rfl

/-! ### Convergence of the characteristic functions -/

/-- Counting the indices below `m` inside `Finset.range M`, for `m ≤ M`. -/
