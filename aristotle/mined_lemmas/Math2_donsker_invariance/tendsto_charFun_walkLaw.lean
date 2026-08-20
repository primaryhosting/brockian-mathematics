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

theorem tendsto_charFun_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (ht : Monotone t) (ht0 : 0 ≤ t 0) (s : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n ↦ charFun (walkLaw μ t k n) s) atTop (𝓝 (charFun (bmLaw t k) s)) := by
  set S := ∑ j : Fin k, |s j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  set A : ℕ → ℝ := fun n ↦ S / Real.sqrt n with hA
  have hA0 : ∀ n, 0 ≤ A n := fun n ↦ div_nonneg hS0 (Real.sqrt_nonneg _)
  have hAtend : Tendsto A atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  set V : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i ^ 2 with hV
  have hVtend : Tendsto V atTop (𝓝 (∑ l ∈ Finset.range k, bmCoef t k s l ^ 2)) :=
    tendsto_sum_sq_walkCoef ht ht0 s
  set G : ℕ → ℂ := fun n ↦ Complex.exp (-((V n : ℝ) : ℂ) / 2) with hG
  have hGtend : Tendsto G atTop (𝓝 (charFun (bmLaw t k) s)) := by
    rw [charFun_bmLaw]
    exact (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp hVtend).neg.div_const 2)
  have hprodG : ∀ n, G n = ∏ i ∈ Finset.range (stepCount t n k),
      Complex.exp (-((walkCoef t k n s i : ℂ)) ^ 2 / 2) := by
    intro n
    have hcast : ((V n : ℝ) : ℂ)
        = ∑ i ∈ Finset.range (stepCount t n k), ((walkCoef t k n s i : ℂ)) ^ 2 := by
      rw [hV]; push_cast; rfl
    rw [hG]
    simp only
    rw [hcast, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ ↦ by ring_nf
  have hbound : ∀ n, ‖charFun (walkLaw μ t k n) s - G n‖
      ≤ V n * (taylorErr μ (A n) + A n ^ 2) := by
    intro n
    rw [charFun_walkLaw μ ht n s, hprodG n]
    have hexp_le : ∀ a : ℝ, ‖Complex.exp (-((a : ℂ)) ^ 2 / 2)‖ ≤ 1 := by
      intro a
      have hc : (-((a : ℂ)) ^ 2 / 2) = ((-(a ^ 2) / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [sq_nonneg a]
    refine (norm_prod_sub_prod_le _ _ _ (fun i _ ↦ norm_charFun_le_one _)
      (fun i _ ↦ hexp_le _)).trans ?_
    have hterm : ∀ i, ‖charFun μ (walkCoef t k n s i)
        - Complex.exp (-((walkCoef t k n s i : ℂ)) ^ 2 / 2)‖
        ≤ walkCoef t k n s i ^ 2 * (taylorErr μ (A n) + A n ^ 2) := by
      intro i
      set a := walkCoef t k n s i with ha
      have habs : |a| ≤ A n := abs_walkCoef_le n s i
      have h1 : ‖charFun μ a - (1 - (a : ℂ) ^ 2 / 2)‖ ≤ a ^ 2 * taylorErr μ (A n) := by
        refine (norm_charFun_sub_le μ hint hmean hvar a).trans ?_
        exact mul_le_mul_of_nonneg_left
          (taylorErr_mono μ hint (abs_nonneg a) habs) (sq_nonneg a)
      have h2 : ‖(1 - (a : ℂ) ^ 2 / 2) - Complex.exp (-((a : ℂ) ^ 2) / 2)‖ ≤ a ^ 2 * A n ^ 2 := by
        rw [norm_sub_rev]
        refine (norm_exp_sub_one_sub_le a).trans ?_
        have hpow : a ^ 4 = a ^ 2 * a ^ 2 := by ring
        have hsq : a ^ 2 ≤ A n ^ 2 := by
          nlinarith [sq_abs a, abs_nonneg a, hA0 n]
        rw [hpow]
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
      have h3 : charFun μ a - Complex.exp (-((a : ℂ)) ^ 2 / 2)
          = (charFun μ a - (1 - (a : ℂ) ^ 2 / 2))
            + ((1 - (a : ℂ) ^ 2 / 2) - Complex.exp (-((a : ℂ) ^ 2) / 2)) := by ring
      rw [h3]
      refine (norm_add_le _ _).trans ?_
      have := add_le_add h1 h2
      calc ‖charFun μ a - (1 - (a : ℂ) ^ 2 / 2)‖
            + ‖(1 - (a : ℂ) ^ 2 / 2) - Complex.exp (-((a : ℂ) ^ 2) / 2)‖
          ≤ a ^ 2 * taylorErr μ (A n) + a ^ 2 * A n ^ 2 := this
        _ = a ^ 2 * (taylorErr μ (A n) + A n ^ 2) := by ring
    refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_
    rw [← Finset.sum_mul, hV]
  have hzero : Tendsto (fun n ↦ charFun (walkLaw μ t k n) s - G n) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    have hlim := hVtend.mul ((tendsto_taylorErr μ hint A hA0 hAtend).add
      ((hAtend.pow 2).congr fun n ↦ rfl))
    simpa using hlim
  have hfinal := hzero.add hGtend
  rw [zero_add] at hfinal
  exact hfinal.congr fun n ↦ by ring

end Math2

import Mathlib

/-!
# Lévy's continuity theorem for tight sequences

The main result of this file, `Math2.tendsto_integral_of_tendsto_charFun`, says that a
tight sequence of probability measures on a finite-dimensional inner product space whose
characteristic functions converge pointwise to the characteristic function of a probability
measure `ν` converges weakly to `ν`.

This is the form of Lévy's continuity theorem that is needed for Donsker's invariance principle.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace Math2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- The bounded continuous function `x ↦ exp (i ⟪x, s⟫)`, whose integral against a measure is the
characteristic function of that measure at `s`. -/
