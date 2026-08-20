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

theorem donsker_invariance_law
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (htmono : Monotone t)
    {k : ℕ} {f : (Fin k → ℝ) → ℝ} (hf : Continuous f) {C : ℝ} (hfb : ∀ x, |f x| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (fun j : Fin k ↦
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t (j : ℕ)⌋₊, X i ω) / Real.sqrt n) ∂P)
      atTop (𝓝 (∫ x, f (ofLp x) ∂(wienerFdd k t))) := by
  classical
  set u : ℕ → ℝ := shiftTimes t with hu
  have hu0 : u 0 = 0 := shiftTimes_zero t
  have hut : ∀ i : ℕ, u (i + 1) = t i := shiftTimes_succ t
  have humono : Monotone u := monotone_shiftTimes ht0 htmono
  have hunn : ∀ i : ℕ, 0 ≤ u i := shiftTimes_nonneg ht0 htmono
  set σ : Fin k → ℝ := fun i ↦ Real.sqrt (u ((i : ℕ) + 1) - u (i : ℕ)) with hσ
  set σn : ℕ → Fin k → ℝ := fun n i ↦ Real.sqrt ((⌊(n : ℝ) * u ((i : ℕ) + 1)⌋₊ : ℝ) / n
    - (⌊(n : ℝ) * u (i : ℕ)⌋₊ : ℝ) / n) with hσn
  -- the rescaled walk at the given times
  have hleft : ∀ n : ℕ, 1 ≤ n →
      (∫ ω, f (fun j : Fin k ↦
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t (j : ℕ)⌋₊, X i ω) / Real.sqrt n) ∂P)
        = ∫ z, f (stepMap (σn n) z) ∂(stdGaussianPi k) := by
    intro n hn
    have hV : Measurable (fun ω ↦ (toLp 2 (fun j : Fin k ↦
        (∑ i ∈ Finset.range ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :
          EuclideanSpace ℝ (Fin k))) := by
      apply (PiLp.continuous_toLp 2 _).measurable.comp
      exact measurable_pi_lambda _ fun j ↦
        (Finset.measurable_sum _ (fun i _ ↦ hmeas i)).div_const _
    have h := integral_eq_integral_stepMap hV
      (map_walk_eq_gaussVec hmeas hindep hlaw u hu0 humono hn) hf
    simpa [hut] using h
  -- the limit
  have hright : (∫ x, f (ofLp x) ∂(wienerFdd k t)) = ∫ z, f (stepMap σ z) ∂(stdGaussianPi k) := by
    have h := integral_eq_integral_stepMap (P := wienerFdd k t) (V := id) measurable_id
      (σ := σ) (by rw [Measure.map_id, wienerFdd]) hf
    simpa using h
  rw [hright]
  -- convergence of the increments of the rescaled walk
  have hfloor : ∀ a : ℝ, 0 ≤ a → Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * a⌋₊ : ℝ) / n) atTop (𝓝 a) := by
    intro a ha
    have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, mul_comm] using h
  have hσconv : ∀ i : Fin k, Tendsto (fun n ↦ σn n i) atTop (𝓝 (σ i)) := fun i ↦
    ((hfloor _ (hunn ((i : ℕ) + 1))).sub (hfloor _ (hunn (i : ℕ)))).sqrt
  have hpt : ∀ z, Tendsto (fun n ↦ f (stepMap (σn n) z)) atTop (𝓝 (f (stepMap σ z))) := by
    intro z
    have hstep : Tendsto (fun n ↦ stepMap (σn n) z) atTop (𝓝 (stepMap σ z)) := by
      rw [tendsto_pi_nhds]
      intro j
      refine tendsto_finset_sum _ fun i _ ↦ ?_
      by_cases hij : i ≤ j
      · simp only [hij, if_true]
        exact (hσconv i).mul tendsto_const_nhds
      · simp only [hij, if_false]
        exact tendsto_const_nhds
    exact (hf.tendsto (stepMap σ z)).comp hstep
  refine Tendsto.congr' ?_ (tendsto_integral_of_dominated_convergence (fun _ ↦ C)
    (fun n ↦ (hf.comp (continuous_stepMap (σn n))).aestronglyMeasurable)
    (integrable_const C)
    (fun n ↦ Eventually.of_forall fun z ↦ by
      simpa only [Real.norm_eq_abs] using hfb (stepMap (σn n) z))
    (Eventually.of_forall hpt))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hleft n hn).symm

/-- **Donsker's invariance principle** (convergence of the finite dimensional distributions,
for a random walk with standard Gaussian steps).

Let `(X i)` be independent standard Gaussian random variables, let
`S n = X 0 + ⋯ + X (n-1)` be the associated random walk and let
`W n t = S ⌊n t⌋ / √n` be the walk rescaled diffusively.  Let `B` be a Brownian motion.
Then for every nondecreasing sequence of nonnegative times `t 0 ≤ t 1 ≤ ⋯` and every
bounded continuous function `f` on `ℝ^k`,
`E[f (W n (t 0), …, W n (t (k-1)))] → E[f (B (t 0), …, B (t (k-1)))]`,
i.e. the finite dimensional distributions of the rescaled walk converge weakly to those of
Brownian motion. -/
