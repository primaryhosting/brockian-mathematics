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

theorem isTightMeasureSet_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (ht : Monotone t) (ht0 : 0 ≤ t 0) :
    IsTightMeasureSet {walkLaw μ t k n | n : ℕ} := by
  set C := ∑ j : Fin k, (t j + 1) with hC
  have hC0 : 0 ≤ C := by
    refine Finset.sum_nonneg fun j _ ↦ ?_
    have : 0 ≤ t j := ht0.trans (ht (Nat.zero_le j))
    linarith
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have hbound : ∀ r : ℝ, 0 < r →
      (⨆ ν ∈ {walkLaw μ t k n | n : ℕ}, ν {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖})
        ≤ ENNReal.ofReal (C / r ^ 2) := by
    intro r hr
    refine iSup₂_le ?_
    rintro ν ⟨n, rfl⟩
    have hmono : {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}
        ⊆ {x : EuclideanSpace ℝ (Fin k) | r ^ 2 ≤ ‖x‖ ^ 2} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      nlinarith [norm_nonneg x]
    have hmarkov : r ^ 2 * (walkLaw μ t k n).real
        {x : EuclideanSpace ℝ (Fin k) | r ^ 2 ≤ ‖x‖ ^ 2} ≤ C := by
      refine le_trans (mul_meas_ge_le_integral_of_nonneg
        (ae_of_all _ fun x ↦ by positivity) (integrable_norm_sq_walkLaw μ hint n) (r ^ 2)) ?_
      exact integral_sq_norm_walkLaw_le μ hint hmean hvar ht ht0 n
    have hreal : (walkLaw μ t k n).real {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}
        ≤ C / r ^ 2 := by
      refine le_trans (measureReal_mono hmono) ?_
      rw [le_div_iff₀ (by positivity)]
      linarith [hmarkov]
    calc (walkLaw μ t k n) {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}
        = ENNReal.ofReal ((walkLaw μ t k n).real {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (C / r ^ 2) := ENNReal.ofReal_le_ofReal hreal
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (C / r ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ ↦ C / r ^ 2) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop two_ne_zero)
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun r ↦ zero_le _) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr using hbound r hr

end Math2

import RequestProject.Donsker.CharFun

/-!
# The central limit estimate

We prove that the characteristic functions of the rescaled walk converge pointwise to the
characteristic function of the finite-dimensional distribution of Brownian motion.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace Math2

variable {k : ℕ} {t : ℕ → ℝ}

/-! ### Elementary estimates -/

/-- Elementary estimate: a product of complex numbers of modulus at most one depends on its
factors in a Lipschitz way. -/
