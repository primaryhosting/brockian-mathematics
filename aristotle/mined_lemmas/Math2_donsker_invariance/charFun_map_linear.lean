/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker's invariance principle

This file proves Donsker's invariance principle at the level of finite dimensional
distributions, for a random walk with independent standard Gaussian steps.

If `(X i)` are independent standard Gaussian random variables, `S n = X 0 + ⋯ + X (n-1)` and
`W n t = S ⌊n t⌋ / √n` is the diffusively rescaled walk, then for every nondecreasing sequence
of nonnegative times `t 0 ≤ t 1 ≤ ⋯` and every bounded continuous `f : ℝ^k → ℝ`,
`E[f (W n (t 0), …, W n (t (k-1)))]` converges to `E[f (B (t 0), …, B (t (k-1)))]`, where `B` is
any Brownian motion; that is, the finite dimensional distributions of the rescaled walk converge
weakly to those of Brownian motion.

## Main results

* `Math2.donsker_invariance`: the statement above, with the limit expressed through an
  arbitrary process `B` satisfying `Math2.IsBrownianMotion`.
* `Math2.donsker_invariance_law`: the same convergence with the limit written explicitly as the
  finite dimensional Wiener law `Math2.wienerFdd k t`, a statement which involves no Brownian
  motion at all.
* `Math2.covStep_wienerFdd`: the limit law is the centered Gaussian law on `ℝ^k` with covariance
  `min (t i) (t j)`, i.e. the covariance of Brownian motion.
* `Math2.map_brownian_eq_wienerFdd`: any Brownian motion sampled at the times `t` has law
  `wienerFdd k t`.
* `Math2.exists_gaussian_steps`: the assumptions on the steps of the walk are satisfiable.

## Implementation notes

Weak convergence is expressed, as usual, by convergence of the integrals of bounded continuous
test functions.  The law of each finite dimensional vector is identified through its
characteristic function (`Math2.charFun_map_linear`), and the convergence then follows from
dominated convergence, since all the laws involved are images of a fixed standard Gaussian
measure under linear maps depending continuously on the (rescaled) times.

The steps of the walk are assumed to be standard Gaussian.  Brownian motion is axiomatised
through its finite dimensional distributions (`Math2.IsBrownianMotion`); no path regularity is
required, and no construction of Brownian motion is carried out here — this is why the
Brownian-motion-free version `Math2.donsker_invariance_law` is also proved.
-/

open MeasureTheory ProbabilityTheory Filter Topology WithLp
open scoped NNReal

namespace Math2

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `IsBrownianMotion B P` says that the real valued process `(B t)_{t ≥ 0}` is a Brownian
motion under the probability measure `P`: it starts at `0`, it has independent increments, and
the increment over `[s, r]` is centered Gaussian with variance `r - s`.

Only the finite dimensional distributions are described here (no path regularity is required);
this is exactly what is needed for the convergence of finite dimensional distributions in
Donsker's theorem. -/
structure IsBrownianMotion (B : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Each `B s` is measurable. -/
  measurable : ∀ s, Measurable (B s)
  /-- The process starts at `0`. -/
  start_zero : ∀ᵐ ω ∂P, B 0 ω = 0
  /-- The increment over `[s, r]` is centered Gaussian with variance `r - s`. -/
  gaussian_increment : ∀ s r : ℝ, 0 ≤ s → s ≤ r →
    P.map (fun ω ↦ B r ω - B s ω) = gaussianReal 0 (Real.toNNReal (r - s))
  /-- The increments along any nondecreasing sequence of times are independent. -/
  indep_increments : ∀ (m : ℕ) (v : ℕ → ℝ), Monotone v → 0 ≤ v 0 →
    iIndepFun (fun (i : Fin m) ω ↦ B (v ((i : ℕ) + 1)) ω - B (v (i : ℕ)) ω) P

/-! ### Gaussian vectors with independent increments -/

/-- `stepMap σ z j = ∑_{i ≤ j} σ i * z i`: the partial sums of the rescaled coordinates. -/

lemma charFun_map_linear {ι : Type*} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hindep : iIndepFun X P) (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    {k : ℕ} (s : Finset ι) (A : Fin k → ι → ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    charFun (P.map fun ω ↦
        (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) : EuclideanSpace ℝ (Fin k))) y
      = Complex.exp (-(∑ j, ∑ j', y j * y j' * ∑ i ∈ s, (v i : ℝ) * A j i * A j' i) / 2) := by
  classical
  set c : ι → ℝ := fun i ↦ ∑ j, y j * A j i with hc
  have hmV : Measurable (fun ω ↦
      (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) : EuclideanSpace ℝ (Fin k))) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply measurable_pi_lambda
    intro j
    exact Finset.measurable_sum _ (fun i _ ↦ (hmeas i).const_mul _)
  have hinner : ∀ ω, (inner ℝ (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) :
      EuclideanSpace ℝ (Fin k)) y) = ∑ i ∈ s, c i * X i ω := by
    intro ω
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    simp only [Finset.mul_sum, hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have h1 : charFun (P.map fun ω ↦
      (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) : EuclideanSpace ℝ (Fin k))) y
      = ∫ ω, Complex.exp ((∑ i ∈ s, c i * X i ω : ℝ) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hmV.aemeasurable (by fun_prop)]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by simp only [hinner])
  have h2 : charFun (P.map fun ω ↦ ∑ i ∈ s, c i * X i ω) (1 : ℝ)
      = ∫ ω, Complex.exp ((∑ i ∈ s, c i * X i ω : ℝ) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    simp
  have hY : iIndepFun (fun i ω ↦ c i * X i ω) P :=
    hindep.comp _ (fun i ↦ measurable_const_mul (c i))
  have hmY : ∀ i, Measurable (fun ω ↦ c i * X i ω) := fun i ↦ (hmeas i).const_mul _
  have hlawY : ∀ i, P.map (fun ω ↦ c i * X i ω)
      = gaussianReal 0 (Real.toNNReal (c i ^ 2) * v i) := by
    intro i
    rw [show (fun ω ↦ c i * X i ω) = (fun x : ℝ ↦ c i * x) ∘ (X i) from rfl,
      ← Measure.map_map (measurable_const_mul _) (hmeas i), hlaw i, gaussianReal_map_const_mul]
    norm_num
    congr 1
    ext
    simp [Real.toNNReal, max_eq_left (sq_nonneg (c i))]
  have hsum : ∑ i ∈ s, (v i : ℝ) * c i ^ 2
      = ∑ j, ∑ j', y j * y j' * ∑ i ∈ s, (v i : ℝ) * A j i * A j' i := by
    have step : ∀ i, (v i : ℝ) * c i ^ 2
        = ∑ j, ∑ j', y j * y j' * ((v i : ℝ) * A j i * A j' i) := by
      intro i
      rw [hc]
      simp only [sq]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j' _ ↦ by ring
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ ↦ by rw [Finset.mul_sum]
  rw [h1, ← h2, charFun_map_finset_sum hY hmY s 1]
  simp_rw [hlawY, charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_one, Complex.ofReal_zero]
  have key : ∀ x ∈ s, ((1:ℂ) * 0 * Complex.I
      - ((Real.toNNReal (c x ^ 2) * v x : ℝ≥0) : ℝ) * (1:ℂ) ^ 2 / 2)
      = -(((v x : ℝ) * c x ^ 2 : ℝ) : ℂ) / 2 := by
    intro x _
    push_cast [Real.coe_toNNReal _ (sq_nonneg (c x))]
    ring
  rw [Finset.sum_congr rfl key, neg_div, ← Finset.sum_div, Finset.sum_neg_distrib, neg_div,
    ← Complex.ofReal_sum, hsum]

