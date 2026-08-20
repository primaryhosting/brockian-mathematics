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
def stepMap {k : ℕ} (σ : Fin k → ℝ) (z : Fin k → ℝ) : Fin k → ℝ :=
  fun j ↦ ∑ i, if i ≤ j then σ i * z i else 0

/-- The standard Gaussian measure on `Fin k → ℝ`. -/
def stdGaussianPi (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi fun _ ↦ gaussianReal 0 1

instance (k : ℕ) : IsProbabilityMeasure (stdGaussianPi k) := by
  unfold stdGaussianPi; infer_instance

/-- The law of the centered Gaussian vector `(∑_{i ≤ j} σ i Z i)_j`, where the `Z i` are
independent standard Gaussians. -/
def gaussVec {k : ℕ} (σ : Fin k → ℝ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (stdGaussianPi k).map fun z ↦ (toLp 2 (stepMap σ z) : EuclideanSpace ℝ (Fin k))

/-- The covariance of the Gaussian vector `gaussVec σ`. -/
def covStep {k : ℕ} (σ : Fin k → ℝ) (j j' : Fin k) : ℝ :=
  ∑ i, if i ≤ j ∧ i ≤ j' then σ i ^ 2 else 0

/-! ### Characteristic function computations -/

/-- The characteristic function of a finite sum of independent real random variables is the
product of the characteristic functions. -/
lemma charFun_map_finset_sum {ι : Type*} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} (hindep : iIndepFun X P) (hmeas : ∀ i, Measurable (X i))
    (s : Finset ι) (y : ℝ) :
    charFun (P.map fun ω ↦ ∑ i ∈ s, X i ω) y = ∏ i ∈ s, charFun (P.map (X i)) y := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    rw [Measure.map_const]
    simp [charFun_dirac]
  | insert a s ha ih =>
    have h1 : (fun ω ↦ ∑ i ∈ insert a s, X i ω) = (fun ω ↦ ∑ i ∈ s, X i ω) + X a := by
      funext ω; simp [Finset.sum_insert ha, add_comm]
    have hind : (fun ω ↦ ∑ i ∈ s, X i ω) ⟂ᵢ[P] X a := by
      have h := hindep.indepFun_finset_sum_of_notMem hmeas ha
      have he : (∑ j ∈ s, X j) = (fun ω ↦ ∑ i ∈ s, X i ω) := by
        funext ω; simp [Finset.sum_apply]
      rwa [he] at h
    rw [h1, IndepFun.charFun_map_add_eq_mul (by fun_prop) (hmeas a).aemeasurable hind]
    rw [Pi.mul_apply, ih, Finset.prod_insert ha, mul_comm]

/-- The characteristic function of a linear image of a family of independent centered Gaussian
random variables. -/
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

lemma continuous_stepMap {k : ℕ} (σ : Fin k → ℝ) : Continuous (stepMap σ) := by
  unfold stepMap
  refine continuous_pi fun j ↦ continuous_finset_sum _ fun i _ ↦ ?_
  by_cases h : i ≤ j <;> simp only [h, if_true, if_false] <;> fun_prop

instance {k : ℕ} (σ : Fin k → ℝ) : IsProbabilityMeasure (gaussVec σ) := by
  rw [gaussVec]
  exact Measure.isProbabilityMeasure_map
    (((PiLp.continuous_toLp 2 _).comp (continuous_stepMap σ)).measurable).aemeasurable

lemma charFun_gaussVec {k : ℕ} (σ : Fin k → ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    charFun (gaussVec σ) y
      = Complex.exp (-(∑ j, ∑ j', y j * y j' * covStep σ j j') / 2) := by
  classical
  have hcoord : ∀ i : Fin k, Measurable (fun z : Fin k → ℝ ↦ z i) :=
    fun i ↦ measurable_pi_apply i
  have hlaw : ∀ i : Fin k, (stdGaussianPi k).map (fun z : Fin k → ℝ ↦ z i) = gaussianReal 0 1 :=
    fun i ↦ (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin k ↦ gaussianReal 0 1) i).map_eq
  have hindep : iIndepFun (fun (i : Fin k) (z : Fin k → ℝ) ↦ z i) (stdGaussianPi k) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hcoord i).aemeasurable)]
    simp only [hlaw]
    rw [show (fun (z : Fin k → ℝ) (i : Fin k) ↦ z i) = id from rfl, Measure.map_id]
    rfl
  have hgv : gaussVec σ = (stdGaussianPi k).map (fun z ↦
      (toLp 2 (fun j ↦ ∑ i ∈ Finset.univ, (if i ≤ j then σ i else 0) * z i) :
        EuclideanSpace ℝ (Fin k))) := by
    rw [gaussVec]
    congr 1
    funext z
    congr 1
    funext j
    rw [stepMap]
    exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring
  have hcov : ∀ j j' : Fin k, (∑ i ∈ Finset.univ, ((1 : ℝ≥0) : ℝ) *
      (if i ≤ j then σ i else 0) * (if i ≤ j' then σ i else 0)) = covStep σ j j' := by
    intro j j'
    rw [covStep]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h1 : i ≤ j <;> by_cases h2 : i ≤ j' <;> simp [h1, h2, sq]
  rw [hgv, charFun_map_linear hindep hcoord (v := fun _ ↦ 1) hlaw Finset.univ
    (fun j i ↦ if i ≤ j then σ i else 0) y]
  simp only [hcov]

/-- A vector of linear combinations of independent centered Gaussians is distributed as
`gaussVec σ`, as soon as the covariances agree. -/
lemma map_eq_gaussVec {ι : Type*} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hindep : iIndepFun X P) (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    {k : ℕ} (s : Finset ι) (A : Fin k → ι → ℝ) (σ : Fin k → ℝ)
    (hcov : ∀ j j', ∑ i ∈ s, (v i : ℝ) * A j i * A j' i = covStep σ j j') :
    (P.map fun ω ↦ (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) : EuclideanSpace ℝ (Fin k)))
      = gaussVec σ := by
  classical
  have hmV : Measurable (fun ω ↦
      (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) : EuclideanSpace ℝ (Fin k))) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    exact measurable_pi_lambda _ fun j ↦
      Finset.measurable_sum _ (fun i _ ↦ (hmeas i).const_mul _)
  haveI : IsProbabilityMeasure (P.map fun ω ↦
      (toLp 2 (fun j ↦ ∑ i ∈ s, A j i * X i ω) : EuclideanSpace ℝ (Fin k))) :=
    Measure.isProbabilityMeasure_map hmV.aemeasurable
  refine Measure.ext_of_charFun ?_
  funext y
  rw [charFun_map_linear hindep hmeas hlaw s A y, charFun_gaussVec]
  simp only [hcov]

/-! ### The covariance of a process with independent increments -/

/-- The covariance of the Gaussian vector whose increments have variances `h (i+1) - h i`. -/
lemma covStep_sqrt_diff {k : ℕ} (h : ℕ → ℝ) (hmono : Monotone h) (j j' : Fin k) :
    covStep (fun i : Fin k ↦ Real.sqrt (h ((i : ℕ) + 1) - h (i : ℕ))) j j'
      = h ((min j j' : Fin k) + 1) - h 0 := by
  set J : ℕ := ((min j j' : Fin k) : ℕ) with hJ
  have hJk : J < k := (min j j').isLt
  have step : ∀ i : Fin k,
      (if i ≤ j ∧ i ≤ j' then (Real.sqrt (h ((i : ℕ) + 1) - h (i : ℕ))) ^ 2 else 0)
      = (if (i : ℕ) ≤ J then h ((i : ℕ) + 1) - h (i : ℕ) else 0) := by
    intro i
    have hsq : (Real.sqrt (h ((i : ℕ) + 1) - h (i : ℕ))) ^ 2 = h ((i : ℕ) + 1) - h (i : ℕ) :=
      Real.sq_sqrt (by simp only [sub_nonneg]; exact hmono (Nat.le_succ _))
    rw [hsq]
    congr 1
    simp only [hJ, Fin.le_def, Fin.coe_min, le_min_iff]
  rw [covStep]
  simp only [step]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i ≤ J then h (i + 1) - h i else 0) k,
    ← Finset.sum_filter]
  have hf : (Finset.range k).filter (fun i ↦ i ≤ J) = Finset.range (J + 1) := by
    ext x; simp; omega
  rw [hf, Finset.sum_range_sub h]

/-! ### The law of the rescaled random walk and of the Brownian vector -/

/-- The law of the rescaled random walk sampled at times `t 0 ≤ t 1 ≤ ...`. -/
lemma map_walk_eq_gaussVec {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {k : ℕ} (u : ℕ → ℝ) (hu0 : u 0 = 0) (humono : Monotone u) {n : ℕ} (hn : 1 ≤ n) :
    (P.map fun ω ↦ (toLp 2 (fun j : Fin k ↦
        (∑ i ∈ Finset.range ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :
          EuclideanSpace ℝ (Fin k)))
      = gaussVec (fun i : Fin k ↦
          Real.sqrt ((⌊(n : ℝ) * u ((i : ℕ) + 1)⌋₊ : ℝ) / n - (⌊(n : ℝ) * u (i : ℕ)⌋₊ : ℝ) / n)) := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set m : ℕ → ℕ := fun i ↦ ⌊(n : ℝ) * u i⌋₊ with hm
  have hmmono : Monotone m := fun a b hab ↦ Nat.floor_le_floor (by nlinarith [humono hab])
  have hm0 : m 0 = 0 := by simp [hm, hu0]
  set h : ℕ → ℝ := fun i ↦ (m i : ℝ) / n with hh
  have hhmono : Monotone h := by
    intro a b hab
    have : (m a : ℝ) ≤ m b := by exact_mod_cast hmmono hab
    simp only [hh]
    gcongr
  set A : Fin k → ℕ → ℝ := fun j i ↦ if i < m ((j : ℕ) + 1) then (Real.sqrt n)⁻¹ else 0 with hA
  set N : ℕ := m k with hN
  have hmle : ∀ j : Fin k, m ((j : ℕ) + 1) ≤ N := fun j ↦ hmmono (by omega)
  have hfun : (fun ω ↦ (toLp 2 (fun j : Fin k ↦
      (∑ i ∈ Finset.range (m ((j : ℕ) + 1)), X i ω) / Real.sqrt n) : EuclideanSpace ℝ (Fin k)))
      = (fun ω ↦ (toLp 2 (fun j : Fin k ↦ ∑ i ∈ Finset.range N, A j i * X i ω) :
        EuclideanSpace ℝ (Fin k))) := by
    funext ω
    congr 1
    funext j
    have hstep : ∀ i, A j i * X i ω
        = if i < m ((j : ℕ) + 1) then (Real.sqrt n)⁻¹ * X i ω else 0 := by
      intro i; simp only [hA]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), ← Finset.sum_filter]
    have hf : (Finset.range N).filter (fun i ↦ i < m ((j : ℕ) + 1))
        = Finset.range (m ((j : ℕ) + 1)) := by
      have := hmle j; ext x; simp; omega
    rw [hf, ← Finset.mul_sum, inv_mul_eq_div]
  rw [show (fun ω ↦ (toLp 2 (fun j : Fin k ↦
      (∑ i ∈ Finset.range ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :
        EuclideanSpace ℝ (Fin k)))
      = (fun ω ↦ (toLp 2 (fun j : Fin k ↦
      (∑ i ∈ Finset.range (m ((j : ℕ) + 1)), X i ω) / Real.sqrt n) :
        EuclideanSpace ℝ (Fin k))) from rfl, hfun,
    show (fun i : Fin k ↦ Real.sqrt ((⌊(n : ℝ) * u ((i : ℕ) + 1)⌋₊ : ℝ) / n
      - (⌊(n : ℝ) * u (i : ℕ)⌋₊ : ℝ) / n))
      = (fun i : Fin k ↦ Real.sqrt (h ((i : ℕ) + 1) - h (i : ℕ))) from rfl]
  refine map_eq_gaussVec hindep hmeas hlaw (Finset.range N) A _ ?_
  intro j j'
  rw [covStep_sqrt_diff h hhmono j j']
  have hstep : ∀ i, ((1:ℝ≥0):ℝ) * A j i * A j' i
      = if i < min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1)) then ((Real.sqrt n)⁻¹) ^ 2 else 0 := by
    intro i
    simp only [hA]
    by_cases h1 : i < m ((j : ℕ) + 1) <;> by_cases h2 : i < m ((j' : ℕ) + 1) <;>
      simp [h1, h2, sq]
  have hmin : min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1)) = m (((min j j' : Fin k) : ℕ) + 1) := by
    rcases le_total j j' with hle | hle
    · rw [min_eq_left hle, min_eq_left (hmmono (Nat.succ_le_succ (Fin.le_def.mp hle)))]
    · rw [min_eq_right hle, min_eq_right (hmmono (Nat.succ_le_succ (Fin.le_def.mp hle)))]
  have hfilter : (Finset.range N).filter (fun i ↦ i < min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1)))
      = Finset.range (min (m ((j : ℕ) + 1)) (m ((j' : ℕ) + 1))) := by
    have h1 := hmle j; have h2 := hmle j'
    ext x; simp; omega
  have hsq : ((Real.sqrt n)⁻¹) ^ 2 = 1 / (n : ℝ) := by
    rw [inv_pow, Real.sq_sqrt hnpos.le]; ring
  rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), ← Finset.sum_filter, hfilter, Finset.sum_const,
    Finset.card_range, hmin, hsq]
  simp only [hh, hm0, nsmul_eq_mul, Nat.cast_zero, zero_div, sub_zero]
  ring

/-- The law of a Brownian motion sampled at times `u 1 ≤ u 2 ≤ ...`. -/
lemma map_brownian_eq_gaussVec {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ → Ω → ℝ}
    (hB : IsBrownianMotion B P) {k : ℕ} (u : ℕ → ℝ) (hu0 : u 0 = 0) (humono : Monotone u) :
    (P.map fun ω ↦ (toLp 2 (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω) :
        EuclideanSpace ℝ (Fin k)))
      = gaussVec (fun i : Fin k ↦ Real.sqrt (u ((i : ℕ) + 1) - u (i : ℕ))) := by
  classical
  have hu0' : (0:ℝ) ≤ u 0 := le_of_eq hu0.symm
  set D : Fin k → Ω → ℝ := fun i ω ↦ B (u ((i : ℕ) + 1)) ω - B (u (i : ℕ)) ω with hD
  have hmeasD : ∀ i, Measurable (D i) := fun i ↦ (hB.measurable _).sub (hB.measurable _)
  have hindep : iIndepFun D P := hB.indep_increments k u humono hu0'
  have hlawD : ∀ i : Fin k, P.map (D i)
      = gaussianReal 0 (Real.toNNReal (u ((i : ℕ) + 1) - u (i : ℕ))) :=
    fun i ↦ hB.gaussian_increment _ _ (hu0 ▸ humono (Nat.zero_le _)) (humono (Nat.le_succ _))
  set A : Fin k → Fin k → ℝ := fun j i ↦ if i ≤ j then 1 else 0 with hA
  have hae : (fun ω ↦ (toLp 2 (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω) :
      EuclideanSpace ℝ (Fin k)))
      =ᵐ[P] (fun ω ↦ (toLp 2 (fun j : Fin k ↦ ∑ i, A j i * D i ω) :
        EuclideanSpace ℝ (Fin k))) := by
    filter_upwards [hB.start_zero] with ω hω
    congr 1
    funext j
    have hstep : ∀ i : Fin k, A j i * D i ω
        = (if (i : ℕ) ≤ (j : ℕ) then B (u ((i : ℕ) + 1)) ω - B (u (i : ℕ)) ω else 0) := by
      intro i
      simp only [hA, hD, Fin.le_def]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hstep i),
      Fin.sum_univ_eq_sum_range
        (fun i ↦ if i ≤ (j : ℕ) then B (u (i + 1)) ω - B (u i) ω else 0) k, ← Finset.sum_filter]
    have hf : (Finset.range k).filter (fun i ↦ i ≤ (j : ℕ)) = Finset.range ((j : ℕ) + 1) := by
      ext x; simp; omega
    rw [hf, Finset.sum_range_sub (fun i ↦ B (u i) ω), hu0, hω]
    ring
  rw [Measure.map_congr hae]
  refine map_eq_gaussVec hindep hmeasD hlawD Finset.univ A _ ?_
  intro j j'
  rw [covStep]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hnn : 0 ≤ u ((i : ℕ) + 1) - u (i : ℕ) := by
    simp only [sub_nonneg]; exact humono (Nat.le_succ _)
  simp only [hA]
  by_cases h1 : i ≤ j <;> by_cases h2 : i ≤ j' <;>
    simp [h1, h2, Real.sq_sqrt hnn, Real.coe_toNNReal _ hnn]

/-- Integrating a bounded continuous function against the law of a Gaussian vector. -/
lemma integral_eq_integral_stepMap {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → EuclideanSpace ℝ (Fin k)} (hV : Measurable V) {σ : Fin k → ℝ}
    (hlaw : P.map V = gaussVec σ) {f : (Fin k → ℝ) → ℝ} (hf : Continuous f) :
    ∫ ω, f (ofLp (V ω)) ∂P = ∫ z, f (stepMap σ z) ∂(stdGaussianPi k) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦ f (ofLp x)) :=
    hf.comp (PiLp.continuous_ofLp 2 _)
  have hm : Measurable (fun z : Fin k → ℝ ↦ (toLp 2 (stepMap σ z) : EuclideanSpace ℝ (Fin k))) :=
    ((PiLp.continuous_toLp 2 _).comp (continuous_stepMap σ)).measurable
  rw [← integral_map hV.aemeasurable hcont.aestronglyMeasurable, hlaw, gaussVec,
    integral_map hm.aemeasurable hcont.aestronglyMeasurable]

/-! ### The finite dimensional distributions of Brownian motion -/

/-- `shiftTimes t` is the sequence of times `0, t 0, t 1, …`. -/
def shiftTimes (t : ℕ → ℝ) : ℕ → ℝ := fun i ↦ if i = 0 then 0 else t (i - 1)

@[simp] lemma shiftTimes_zero (t : ℕ → ℝ) : shiftTimes t 0 = 0 := rfl

@[simp] lemma shiftTimes_succ (t : ℕ → ℝ) (i : ℕ) : shiftTimes t (i + 1) = t i := by
  simp [shiftTimes]

lemma monotone_shiftTimes {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (htmono : Monotone t) :
    Monotone (shiftTimes t) := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · simp only [shiftTimes, if_neg (by omega : b ≠ 0)]
      exact le_trans ht0 (htmono (Nat.zero_le _))
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    simp only [shiftTimes, if_neg (by omega : a ≠ 0), if_neg (by omega : b ≠ 0)]
    exact htmono (by omega)

lemma shiftTimes_nonneg {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (htmono : Monotone t) (i : ℕ) :
    0 ≤ shiftTimes t i :=
  shiftTimes_zero t ▸ monotone_shiftTimes ht0 htmono (Nat.zero_le i)

/-- The finite dimensional distribution of Brownian motion at the times `t 0, …, t (k-1)`:
the centered Gaussian law on `ℝ^k` with covariance `min (t i) (t j)`
(see `covStep_wienerFdd`). -/
def wienerFdd (k : ℕ) (t : ℕ → ℝ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  gaussVec (fun i : Fin k ↦ Real.sqrt (shiftTimes t ((i : ℕ) + 1) - shiftTimes t (i : ℕ)))

instance (k : ℕ) (t : ℕ → ℝ) : IsProbabilityMeasure (wienerFdd k t) := by
  unfold wienerFdd; infer_instance

/-- The covariance of `wienerFdd k t` is `min (t i) (t j)`, the covariance of Brownian motion. -/
lemma covStep_wienerFdd {k : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (htmono : Monotone t) (j j' : Fin k) :
    covStep (fun i : Fin k ↦ Real.sqrt (shiftTimes t ((i : ℕ) + 1) - shiftTimes t (i : ℕ))) j j'
      = min (t (j : ℕ)) (t (j' : ℕ)) := by
  rw [covStep_sqrt_diff _ (monotone_shiftTimes ht0 htmono) j j', shiftTimes_succ,
    shiftTimes_zero, sub_zero, Fin.coe_min]
  rcases le_total (j : ℕ) (j' : ℕ) with hle | hle
  · rw [min_eq_left hle, min_eq_left (htmono hle)]
  · rw [min_eq_right hle, min_eq_right (htmono hle)]

/-- The law of a Brownian motion sampled at the times `t 0, …, t (k-1)` is `wienerFdd k t`. -/
lemma map_brownian_eq_wienerFdd {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ → Ω → ℝ}
    (hB : IsBrownianMotion B P) {k : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (htmono : Monotone t) :
    (P.map fun ω ↦ (toLp 2 (fun j : Fin k ↦ B (t (j : ℕ)) ω) : EuclideanSpace ℝ (Fin k)))
      = wienerFdd k t := by
  have h := map_brownian_eq_gaussVec hB (k := k) (shiftTimes t) (shiftTimes_zero t)
    (monotone_shiftTimes ht0 htmono)
  simpa [wienerFdd] using h

/-! ### Donsker's invariance principle -/

/-- **Donsker's invariance principle**, with the limit law written explicitly as the finite
dimensional Wiener law `wienerFdd k t` (the centered Gaussian law with covariance
`min (t i) (t j)`).  See `donsker_invariance` for the formulation with a Brownian motion. -/
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
theorem donsker_invariance
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion B P')
    {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (htmono : Monotone t)
    {k : ℕ} {f : (Fin k → ℝ) → ℝ} (hf : Continuous f) {C : ℝ} (hfb : ∀ x, |f x| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (fun j : Fin k ↦
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t (j : ℕ)⌋₊, X i ω) / Real.sqrt n) ∂P)
      atTop (𝓝 (∫ ω, f (fun j : Fin k ↦ B (t (j : ℕ)) ω) ∂P')) := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦ f (ofLp x)) :=
    hf.comp (PiLp.continuous_ofLp 2 _)
  have hV : Measurable (fun ω ↦ (toLp 2 (fun j : Fin k ↦ B (t (j : ℕ)) ω) :
      EuclideanSpace ℝ (Fin k))) :=
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun j ↦ hB.measurable _)
  have hBint : (∫ ω, f (fun j : Fin k ↦ B (t (j : ℕ)) ω) ∂P')
      = ∫ x, f (ofLp x) ∂(wienerFdd k t) := by
    rw [← map_brownian_eq_wienerFdd hB ht0 htmono,
      integral_map hV.aemeasurable hcont.aestronglyMeasurable]
  rw [hBint]
  exact donsker_invariance_law hmeas hindep hlaw ht0 htmono hf hfb

/-- The hypotheses on the steps of the random walk are satisfiable: there is a probability space
carrying a sequence of independent standard Gaussian random variables. -/
theorem exists_gaussian_steps :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
        ∀ i, P.map (X i) = gaussianReal 0 1 := by
  obtain ⟨Ω, mΩ, P, X, hmeas, hlaw, hindep, hP⟩ := exists_iid ℕ (gaussianReal (0 : ℝ) 1)
  exact ⟨Ω, mΩ, P, X, hP, hmeas, hindep, fun i ↦ (hlaw i).map_eq⟩

end

end Math2

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

