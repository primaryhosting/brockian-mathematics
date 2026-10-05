/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/
noncomputable def donskerInterp {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω)
      + ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) * X ⌊(n : ℝ) * t⌋₊ ω) / Real.sqrt n

/-- The variance of `donskerInterp X n t` when the steps are standard Gaussian:
`(⌊nt⌋ + (nt - ⌊nt⌋)²)/n`. -/
noncomputable def donskerVar (n : ℕ) (t : ℝ) : ℝ≥0 :=
  (((⌊(n : ℝ) * t⌋₊ : ℝ) + ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) ^ 2) / n).toNNReal

/-- `B` is a Brownian motion on the probability space `(Ω, P)`: it starts at `0`, has continuous
paths, independent increments, and `B t - B s` is centred Gaussian with variance `t - s`. -/
structure IsBrownianMotion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ → Ω → ℝ) :
    Prop where
  measurable : ∀ t, Measurable (B t)
  start_zero : ∀ ω, B 0 ω = 0
  continuous_paths : ∀ ω, Continuous fun t ↦ B t ω
  gaussian_increments : ∀ s t, 0 ≤ s → s ≤ t →
    P.map (fun ω ↦ B t ω - B s ω) = gaussianReal 0 (t - s).toNNReal
  indep_increments : ∀ (k : ℕ) (u : ℕ → ℝ), Monotone u → 0 ≤ u 0 →
    iIndepFun (fun i : Fin k ↦ fun ω ↦ B (u (i + 1)) ω - B (u i) ω) P

section Lemmas

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A centred Gaussian measure is the image of the standard Gaussian under scaling by `√v`. -/
lemma gaussianReal_eq_map_sqrt (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x ↦ Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  norm_num
  congr 1

/-- Weak convergence of centred Gaussian laws when the variances converge. -/
lemma tendsto_integral_gaussianReal {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (h : Tendsto (fun n ↦ (v n : ℝ)) atTop (𝓝 (v₀ : ℝ))) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(gaussianReal 0 (v n))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 v₀))) := by
  have key : ∀ w : ℝ≥0,
      ∫ x, f x ∂(gaussianReal 0 w) = ∫ x, f (Real.sqrt w * x) ∂(gaussianReal 0 1) := by
    intro w
    conv_lhs => rw [gaussianReal_eq_map_sqrt w]
    rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
  simp_rw [key]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖) (fun n ↦ ?_) ?_ ?_ ?_
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_const _
  · intro n; exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    exact (f.continuous.tendsto _).comp (((Real.continuous_sqrt.tendsto _).comp h).mul_const x)

/-- The partial sums of i.i.d. standard Gaussians are centred Gaussian with variance `m`. -/
lemma map_partialSum {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (m : ℕ) :
    P.map (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) = gaussianReal 0 m := by
  induction m with
  | zero => simp [Measure.map_const, gaussianReal_zero_var]
  | succ m ih =>
    have hsum : (fun ω ↦ ∑ i ∈ Finset.range (m + 1), X i ω)
        = (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) + X m := by
      funext ω; simp [Finset.sum_range_succ]
    rw [hsum]
    have heq : (∑ j ∈ Finset.range m, X j) = fun ω ↦ ∑ i ∈ Finset.range m, X i ω := by
      funext ω; simp [Finset.sum_apply]
    have hind : IndepFun (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) (X m) P := by
      have h := hindep.indepFun_finset_sum_of_notMem hmeas (s := Finset.range m) (i := m) (by simp)
      rwa [heq] at h
    rw [gaussianReal_add_gaussianReal_of_indepFun hind ih (hlaw m)]
    congr 1
    · simp
    · push_cast; ring

/-- The law of the rescaled interpolated walk is centred Gaussian with variance
`(⌊nt⌋ + (nt - ⌊nt⌋)²)/n`. -/
lemma map_donskerInterp {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (n : ℕ) (t : ℝ) :
    P.map (donskerInterp X n t) = gaussianReal 0 (donskerVar n t) := by
  set m := ⌊(n : ℝ) * t⌋₊ with hm
  set th := (n : ℝ) * t - m with hth
  have hthnn : (0:ℝ) ≤ th ^ 2 := sq_nonneg _
  have hfrac : P.map (fun ω ↦ th * X m ω) = gaussianReal 0 ⟨th ^ 2, hthnn⟩ := by
    rw [show (fun ω ↦ th * X m ω) = (fun x ↦ th * x) ∘ (X m) from rfl,
      ← Measure.map_map (by fun_prop) (hmeas m), hlaw m, gaussianReal_map_const_mul]
    norm_num
  have heq : (∑ j ∈ Finset.range m, X j) = fun ω ↦ ∑ i ∈ Finset.range m, X i ω := by
    funext ω; simp [Finset.sum_apply]
  have hind : IndepFun (fun ω ↦ ∑ i ∈ Finset.range m, X i ω) (fun ω ↦ th * X m ω) P := by
    have h := hindep.indepFun_finset_sum_of_notMem hmeas (s := Finset.range m) (i := m) (by simp)
    rw [heq] at h
    exact h.comp measurable_id (by fun_prop)
  have hY : P.map (fun ω ↦ (∑ i ∈ Finset.range m, X i ω) + th * X m ω)
      = gaussianReal 0 ((m : ℝ≥0) + ⟨th ^ 2, hthnn⟩) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hind
      (map_partialSum hmeas hindep hlaw m) hfrac
    simpa [Pi.add_def] using h
  have hcomp : donskerInterp X n t
      = (fun x ↦ (Real.sqrt n)⁻¹ * x) ∘ (fun ω ↦ (∑ i ∈ Finset.range m, X i ω) + th * X m ω) := by
    funext ω; simp [donskerInterp, div_eq_inv_mul, hm, hth]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hY, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    have h1 : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rw [donskerVar, Real.coe_toNNReal _ (by positivity), h1, ← hm, ← hth]
    ring

/-- The variance of the rescaled walk at time `t` converges to `t`. -/
lemma tendsto_donskerVar {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ((donskerVar n t : ℝ≥0) : ℝ)) atTop (𝓝 t) := by
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ t - (n : ℝ)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun n : ℕ ↦ t + (n : ℝ)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop 0] with n hn
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hinv : (n : ℝ) * ((n : ℝ)⁻¹) = 1 := by field_simp
    have hfl : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (by positivity)
    have hfl2 : (n : ℝ) * t < (⌊(n : ℝ) * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [donskerVar, Real.coe_toNNReal _ (by positivity), le_div_iff₀ hnpos]
    nlinarith [sq_nonneg ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊)]
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hinv : (n : ℝ) * ((n : ℝ)⁻¹) = 1 := by field_simp
    have hfl : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (by positivity)
    have hfl2 : (n : ℝ) * t < (⌊(n : ℝ) * t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [donskerVar, Real.coe_toNNReal _ (by positivity), div_le_iff₀ hnpos]
    have h1 : ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) ^ 2 ≤ 1 := by nlinarith
    nlinarith

lemma measurable_donskerInterp {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (n : ℕ) (t : ℝ) :
    Measurable (donskerInterp X n t) :=
  ((Finset.measurable_sum _ fun i _ ↦ hmeas i).add ((hmeas _).const_mul _)).div_const _

/-- The law of the rescaled walk at time `t` converges weakly to the centred Gaussian law with
variance `t`. -/
lemma tendsto_integral_donskerInterp {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (donskerInterp X n t ω) ∂P) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) := by
  have h2 : ∀ n : ℕ, ∫ ω, f (donskerInterp X n t ω) ∂P
      = ∫ x, f x ∂(gaussianReal 0 (donskerVar n t)) := by
    intro n
    rw [← map_donskerInterp hmeas hindep hlaw n t,
      integral_map (measurable_donskerInterp hmeas n t).aemeasurable
        f.continuous.aestronglyMeasurable]
  simp_rw [h2]
  refine tendsto_integral_gaussianReal ?_ f
  simpa [Real.coe_toNNReal t ht] using tendsto_donskerVar ht

end Lemmas

/-- **Donsker's invariance principle**, one-dimensional time marginals of the polygonal process.

If `X 0, X 1, …` are i.i.d. standard Gaussian random variables and
`W_n(t) = (S_{⌊nt⌋} + (nt-⌊nt⌋)X_{⌊nt⌋})/√n` is the associated rescaled polygonal random walk,
then for every `t ≥ 0` the law of `W_n(t)` converges weakly to the law of `B t`, for any
Brownian motion `B`; that is, `∫ f(W_n(t)) dP → E[f(B t)]` for every bounded continuous `f`. -/
theorem donsker_invariance_marginal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion P' B)
    {t : ℝ} (ht : 0 ≤ t) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (donskerInterp X n t ω) ∂P) atTop
      (𝓝 (∫ ω, f (B t ω) ∂P')) := by
  have hBt : P'.map (B t) = gaussianReal 0 t.toNNReal := by
    have h := hB.gaussian_increments 0 t le_rfl ht
    simpa [hB.start_zero] using h
  have h1 : ∫ ω, f (B t ω) ∂P' = ∫ x, f x ∂(gaussianReal 0 t.toNNReal) := by
    rw [← hBt, integral_map (hB.measurable t).aemeasurable f.continuous.aestronglyMeasurable]
  rw [h1]
  exact tendsto_integral_donskerInterp hmeas hindep hlaw ht f

/-!
## Convergence of the finite-dimensional distributions

We now prove the stronger statement that all finite-dimensional distributions of the rescaled
walk converge to those of Brownian motion.  For this we use the (right-continuous) step version
of the rescaled walk, `donskerStep X n t = S_{⌊nt⌋}/√n`.
-/

/-- The rescaled random walk `t ↦ S_{⌊nt⌋}/√n`. -/
noncomputable def donskerStep {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n

/-- The increment of the rescaled random walk over the time interval `[u j, u (j+1)]`. -/
noncomputable def walkIncr {Ω : Type*} (X : ℕ → Ω → ℝ) (u : ℕ → ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.Ico ⌊(n : ℝ) * u j⌋₊ ⌊(n : ℝ) * u (j + 1)⌋₊, X i ω) / Real.sqrt n

/-- The variance of `walkIncr X u n j` for standard Gaussian steps. -/
noncomputable def walkIncrVar (u : ℕ → ℝ) (n j : ℕ) : ℝ≥0 :=
  (((⌊(n : ℝ) * u (j + 1)⌋₊ - ⌊(n : ℝ) * u j⌋₊ : ℕ) : ℝ) / n).toNNReal

/-- The linear map sending a vector of increments to the vector of its partial sums. -/
noncomputable def cumSumCLM (k : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.pi fun j ↦ ∑ i : Fin k, if (i : ℕ) ≤ (j : ℕ) then LinearMap.proj i else 0)

lemma cumSumCLM_apply {k : ℕ} (y : Fin k → ℝ) (j : Fin k) :
    cumSumCLM k y j = ∑ i : Fin k, if (i : ℕ) ≤ (j : ℕ) then y i else 0 := by
  rw [cumSumCLM]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs <;> simp

lemma sum_fin_le_eq {k : ℕ} (g : ℕ → ℝ) (j : Fin k) :
    ∑ i : Fin k, (if (i : ℕ) ≤ (j : ℕ) then g i else 0)
      = ∑ i ∈ Finset.range ((j : ℕ) + 1), g i := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i ≤ (j : ℕ) then g i else 0) k, ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A product of centred Gaussian measures is the image of the standard Gaussian product measure
under the diagonal scaling by the square roots of the variances. -/
lemma pi_gaussianReal_eq_map_sqrt {k : ℕ} (v : Fin k → ℝ≥0) :
    (Measure.pi fun j : Fin k ↦ gaussianReal 0 (v j))
      = (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1).map fun x j ↦ Real.sqrt (v j) * x j := by
  rw [Measure.pi_map_pi fun j ↦ (by fun_prop :
    AEMeasurable (fun x : ℝ ↦ Real.sqrt (v j) * x) (gaussianReal 0 1))]
  congr 1
  funext j
  exact gaussianReal_eq_map_sqrt (v j)

/-- Weak convergence of products of centred Gaussian laws when the variances converge. -/
lemma tendsto_integral_pi_gaussian {k : ℕ} {v : ℕ → Fin k → ℝ≥0} {w : Fin k → ℝ≥0}
    (h : ∀ j, Tendsto (fun n ↦ ((v n j : ℝ≥0) : ℝ)) atTop (𝓝 ((w j : ℝ≥0) : ℝ)))
    (f : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(Measure.pi fun j ↦ gaussianReal 0 (v n j))) atTop
      (𝓝 (∫ x, f x ∂(Measure.pi fun j ↦ gaussianReal 0 (w j)))) := by
  have hcont : ∀ z : Fin k → ℝ≥0,
      Continuous fun (x : Fin k → ℝ) (j : Fin k) ↦ Real.sqrt (z j) * x j := by
    intro z; fun_prop
  have key : ∀ z : Fin k → ℝ≥0, ∫ x, f x ∂(Measure.pi fun j ↦ gaussianReal 0 (z j))
      = ∫ x, f (fun j ↦ Real.sqrt (z j) * x j) ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1) := by
    intro z
    rw [pi_gaussianReal_eq_map_sqrt z,
      integral_map (hcont z).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  simp_rw [key]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖) (fun n ↦ ?_) ?_ ?_ ?_
  · exact (f.continuous.comp (hcont (v n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n; exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    refine (f.continuous.tendsto _).comp (tendsto_pi_nhds.2 fun j ↦ ?_)
    exact ((Real.continuous_sqrt.tendsto _).comp (h j)).mul_const (x j)

section Fdd

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A sum of i.i.d. standard Gaussians over a finite index set is centred Gaussian with variance
the cardinality of the index set. -/
lemma map_finsetSum {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (s : Finset ℕ) :
    P.map (fun ω ↦ ∑ i ∈ s, X i ω) = gaussianReal 0 s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.map_const, gaussianReal_zero_var]
  | insert a s ha ih =>
    have hsum : (fun ω ↦ ∑ i ∈ insert a s, X i ω) = (fun ω ↦ ∑ i ∈ s, X i ω) + X a := by
      funext ω; simp [Finset.sum_insert ha, add_comm]
    have heq : (∑ j ∈ s, X j) = fun ω ↦ ∑ i ∈ s, X i ω := by
      funext ω; simp [Finset.sum_apply]
    have hind : IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (X a) P := by
      have h := hindep.indepFun_finset_sum_of_notMem hmeas (s := s) (i := a) ha
      rwa [heq] at h
    rw [hsum, gaussianReal_add_gaussianReal_of_indepFun hind ih (hlaw a)]
    congr 1
    · simp
    · rw [Finset.card_insert_of_notMem ha]; push_cast; ring

/-- Sums of an independent family of Gaussian variables over pairwise disjoint blocks are
mutually independent. -/
lemma iIndepFun_blockSums {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {k N : ℕ} (s : Fin k → Finset ℕ) (hsub : ∀ j, s j ⊆ Finset.range N)
    (hs : Pairwise (Function.onFun Disjoint s)) :
    iIndepFun (fun j ω ↦ ∑ i ∈ s j, X i ω) P := by
  classical
  let L : (Fin N → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi fun j ↦ ∑ i : Fin N, if (i : ℕ) ∈ s j then LinearMap.proj i else 0
  have hL : ∀ (v : Fin N → ℝ) (j : Fin k),
      L v j = ∑ i : Fin N, if (i : ℕ) ∈ s j then v i else 0 := by
    intro v j
    simp only [L, LinearMap.pi_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  set L' := LinearMap.toContinuousLinearMap L with hL'
  have hgauss : HasGaussianLaw (fun ω (i : Fin N) ↦ X i ω) P := by
    refine iIndepFun.hasGaussianLaw (fun i ↦ ?_) (hindep.precomp Fin.val_injective)
    exact ⟨by rw [hlaw]; infer_instance⟩
  have hDeq : (fun ω (j : Fin k) ↦ ∑ i ∈ s j, X i ω) = fun ω ↦ L' (fun i : Fin N ↦ X i ω) := by
    funext ω j
    change ∑ i ∈ s j, X i ω = L (fun i : Fin N ↦ X i ω) j
    rw [hL, Fin.sum_univ_eq_sum_range (fun i ↦ if i ∈ s j then X i ω else 0) N,
      Finset.sum_ite_mem]
    congr 1
    exact (Finset.inter_eq_right.2 (hsub j)).symm
  have hDg : HasGaussianLaw (fun ω (j : Fin k) ↦ ∑ i ∈ s j, X i ω) P := by
    rw [hDeq]; exact hgauss.map_fun L'
  refine hDg.iIndepFun_of_covariance_eq_zero fun a b hab ↦ ?_
  have hpair : IndepFun (fun ω ↦ ∑ i ∈ s a, X i ω) (fun ω ↦ ∑ i ∈ s b, X i ω) P := by
    have h := hindep.indepFun_finset (s a) (s b) (hs hab) hmeas
    have h2 := h.comp (φ := fun v : (s a) → ℝ ↦ ∑ i, v i) (ψ := fun v : (s b) → ℝ ↦ ∑ i, v i)
      (by fun_prop) (by fun_prop)
    simpa [Function.comp_def, fun ω ↦ Finset.sum_attach (s a) fun i ↦ X i ω,
      fun ω ↦ Finset.sum_attach (s b) fun i ↦ X i ω] using h2
  exact hpair.covariance_eq_zero (hDg.eval a).memLp_two (hDg.eval b).memLp_two

lemma measurable_walkIncr {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (u : ℕ → ℝ) (n j : ℕ) :
    Measurable (walkIncr X u n j) :=
  (Finset.measurable_sum _ fun i _ ↦ hmeas i).div_const _

/-- The increments of the rescaled walk are centred Gaussian. -/
lemma map_walkIncr {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (u : ℕ → ℝ) (n j : ℕ) :
    P.map (walkIncr X u n j) = gaussianReal 0 (walkIncrVar u n j) := by
  have hcomp : walkIncr X u n j = (fun x ↦ (Real.sqrt n)⁻¹ * x) ∘
      fun ω ↦ ∑ i ∈ Finset.Ico ⌊(n : ℝ) * u j⌋₊ ⌊(n : ℝ) * u (j + 1)⌋₊, X i ω := by
    funext ω; simp [walkIncr, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), map_finsetSum hmeas hindep hlaw,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    have h1 : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rw [walkIncrVar, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), h1,
      Nat.card_Ico]
    ring

/-- The increments of the rescaled walk over disjoint time intervals are independent. -/
lemma iIndepFun_walkIncr {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) {u : ℕ → ℝ} (hu : Monotone u) (n k : ℕ) :
    iIndepFun (fun j : Fin k ↦ walkIncr X u n (j : ℕ)) P := by
  classical
  set s : Fin k → Finset ℕ := fun j ↦
    Finset.Ico ⌊(n : ℝ) * u (j : ℕ)⌋₊ ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊ with hs
  have hmono : ∀ a b : ℕ, a ≤ b → ⌊(n : ℝ) * u a⌋₊ ≤ ⌊(n : ℝ) * u b⌋₊ := fun a b hab ↦
    Nat.floor_le_floor (by nlinarith [hu hab, Nat.cast_nonneg (α := ℝ) n])
  have hsub : ∀ j : Fin k, s j ⊆ Finset.range ⌊(n : ℝ) * u k⌋₊ := by
    intro j x hx
    simp only [hs, Finset.mem_Ico] at hx
    exact Finset.mem_range.2 (lt_of_lt_of_le hx.2 (hmono _ _ (by omega)))
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro a b hab
    have key : ∀ c d : Fin k, (c : ℕ) < (d : ℕ) → Disjoint (s c) (s d) := by
      intro c d hcd
      refine Finset.disjoint_left.2 fun x hx hx' ↦ ?_
      simp only [hs, Finset.mem_Ico] at hx hx'
      have := hmono ((c : ℕ) + 1) (d : ℕ) hcd
      omega
    rcases lt_or_gt_of_ne (fun h ↦ hab (Fin.ext h) : (a : ℕ) ≠ (b : ℕ)) with h | h
    · exact key a b h
    · exact (key b a h).symm
  exact (iIndepFun_blockSums hmeas hindep hlaw s hsub hdisj).comp
    (g := fun _ : Fin k ↦ fun x : ℝ ↦ x / Real.sqrt n) fun _ ↦ by fun_prop

/-- The joint law of the increments of the rescaled walk is a product of centred Gaussians. -/
lemma map_walkIncr_vector {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) {u : ℕ → ℝ} (hu : Monotone u) (n k : ℕ) :
    P.map (fun ω (j : Fin k) ↦ walkIncr X u n (j : ℕ) ω)
      = Measure.pi fun j : Fin k ↦ gaussianReal 0 (walkIncrVar u n (j : ℕ)) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun j ↦
    (measurable_walkIncr hmeas u n (j : ℕ)).aemeasurable).1
      (iIndepFun_walkIncr hmeas hindep hlaw hu n k)]
  congr 1
  funext j
  exact map_walkIncr hmeas hindep hlaw u n (j : ℕ)

/-- The variances of the increments converge to the lengths of the time intervals. -/
lemma tendsto_walkIncrVar {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ ((walkIncrVar u n j : ℝ≥0) : ℝ)) atTop (𝓝 (u (j + 1) - u j)) := by
  have huj : 0 ≤ u j := le_trans hu0 (hu (Nat.zero_le _))
  have huj1 : u j ≤ u (j + 1) := hu (Nat.le_succ _)
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ (u (j + 1) - u j) - (n : ℝ)⁻¹) atTop (𝓝 (u (j + 1) - u j)) := by
    simpa using tendsto_const_nhds.sub hlim
  have hr : Tendsto (fun n : ℕ ↦ (u (j + 1) - u j) + (n : ℝ)⁻¹) atTop (𝓝 (u (j + 1) - u j)) := by
    simpa using tendsto_const_nhds.add hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop 0] with n hn
  all_goals {
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hinv : (n : ℝ) * ((n : ℝ)⁻¹) = 1 := by field_simp
    have hab : ⌊(n : ℝ) * u j⌋₊ ≤ ⌊(n : ℝ) * u (j + 1)⌋₊ := Nat.floor_le_floor (by nlinarith)
    have h1 : (⌊(n : ℝ) * u j⌋₊ : ℝ) ≤ (n : ℝ) * u j := Nat.floor_le (by nlinarith)
    have h2 : (n : ℝ) * u j < (⌊(n : ℝ) * u j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊(n : ℝ) * u (j + 1)⌋₊ : ℝ) ≤ (n : ℝ) * u (j + 1) := Nat.floor_le (by nlinarith)
    have h4 : (n : ℝ) * u (j + 1) < (⌊(n : ℝ) * u (j + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [walkIncrVar, Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Nat.cast_sub hab]
    first
      | (rw [le_div_iff₀ hnpos]; nlinarith)
      | (rw [div_le_iff₀ hnpos]; nlinarith) }

/-- The vector of values of the rescaled walk is the vector of partial sums of its increments. -/
lemma donskerStep_eq_cumSum {X : ℕ → Ω → ℝ} {u : ℕ → ℝ} (hu : Monotone u) (hu0 : u 0 = 0)
    (n k : ℕ) (ω : Ω) :
    (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω)
      = cumSumCLM k fun j : Fin k ↦ walkIncr X u n (j : ℕ) ω := by
  set F : ℕ → ℝ := fun i ↦ ∑ x ∈ Finset.range ⌊(n : ℝ) * u i⌋₊, X x ω with hF
  have hmono : ∀ a b : ℕ, a ≤ b → ⌊(n : ℝ) * u a⌋₊ ≤ ⌊(n : ℝ) * u b⌋₊ := fun a b hab ↦
    Nat.floor_le_floor (by nlinarith [hu hab, Nat.cast_nonneg (α := ℝ) n])
  have hstep : ∀ i : ℕ, walkIncr X u n i ω = (F (i + 1) - F i) / Real.sqrt n := by
    intro i
    rw [walkIncr, hF]
    congr 1
    exact Finset.sum_Ico_eq_sub _ (hmono i (i + 1) (Nat.le_succ i))
  funext j
  rw [cumSumCLM_apply, sum_fin_le_eq (fun i ↦ walkIncr X u n i ω) j]
  simp_rw [hstep]
  rw [← Finset.sum_div, Finset.sum_range_sub F]
  have h0 : F 0 = 0 := by simp [hF, hu0]
  rw [h0, sub_zero]
  rfl

end Fdd

/-- The joint law of the increments of a Brownian motion is a product of centred Gaussians. -/
lemma map_bmIncr_vector {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion P' B)
    {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) (k : ℕ) :
    P'.map (fun ω (j : Fin k) ↦ B (u ((j : ℕ) + 1)) ω - B (u (j : ℕ)) ω)
      = Measure.pi fun j : Fin k ↦ gaussianReal 0 (u ((j : ℕ) + 1) - u (j : ℕ)).toNNReal := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun j ↦
    ((hB.measurable _).sub (hB.measurable _)).aemeasurable).1 (hB.indep_increments k u hu hu0)]
  congr 1
  funext j
  exact hB.gaussian_increments _ _ (le_trans hu0 (hu (Nat.zero_le _))) (hu (Nat.le_succ _))

/-- The vector of values of a Brownian motion is the vector of partial sums of its increments. -/
lemma bm_eq_cumSum {Ω' : Type*} [MeasurableSpace Ω'] {B : ℝ → Ω' → ℝ}
    (hB0 : ∀ ω, B 0 ω = 0) {u : ℕ → ℝ} (hu0 : u 0 = 0) (k : ℕ) (ω : Ω') :
    (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω)
      = cumSumCLM k fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω - B (u (j : ℕ)) ω := by
  funext j
  rw [cumSumCLM_apply, sum_fin_le_eq (fun i ↦ B (u (i + 1)) ω - B (u i) ω) j,
    Finset.sum_range_sub fun i ↦ B (u i) ω, hu0, hB0, sub_zero]

/-- **Donsker's invariance principle** (Gaussian steps): convergence of the finite-dimensional
distributions of the rescaled random walk to those of Brownian motion.

Let `X 0, X 1, …` be i.i.d. standard Gaussian random variables, `S_m = X_0 + ⋯ + X_{m-1}` and
`W_n(t) = S_{⌊nt⌋}/√n` the rescaled random walk.  Let `0 = u 0 ≤ u 1 ≤ u 2 ≤ ⋯` be times and let
`B` be a Brownian motion.  Then the random vector `(W_n(u 1), …, W_n(u k))` converges in
distribution to `(B (u 1), …, B (u k))`: for every bounded continuous `f : (Fin k → ℝ) → ℝ`,
`∫ f(W_n(u 1), …, W_n(u k)) dP → E[f(B (u 1), …, B (u k))]`. -/
theorem donsker_invariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ → Ω' → ℝ} (hB : IsBrownianMotion P' B)
    {u : ℕ → ℝ} (hu : Monotone u) (hu0 : u 0 = 0) (k : ℕ)
    (f : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, f (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω) ∂P) atTop
      (𝓝 (∫ ω, f (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω) ∂P')) := by
  have hu0' : (0 : ℝ) ≤ u 0 := le_of_eq hu0.symm
  set g : BoundedContinuousFunction (Fin k → ℝ) ℝ :=
    f.compContinuous ⟨cumSumCLM k, (cumSumCLM k).continuous⟩ with hg
  have hgapp : ∀ y : Fin k → ℝ, g y = f (cumSumCLM k y) := fun y ↦ rfl
  -- the walk side
  have hleft : ∀ n : ℕ, ∫ ω, f (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω) ∂P
      = ∫ x, g x ∂(Measure.pi fun j : Fin k ↦ gaussianReal 0 (walkIncrVar u n (j : ℕ))) := by
    intro n
    have hpt : ∀ ω, f (fun j : Fin k ↦ donskerStep X n (u ((j : ℕ) + 1)) ω)
        = g fun j : Fin k ↦ walkIncr X u n (j : ℕ) ω := by
      intro ω
      rw [hgapp, ← donskerStep_eq_cumSum hu hu0 n k ω]
    simp_rw [hpt]
    rw [← map_walkIncr_vector hmeas hindep hlaw hu n k,
      integral_map (measurable_pi_lambda _ fun j ↦ measurable_walkIncr hmeas u n (j : ℕ)).aemeasurable
        g.continuous.aestronglyMeasurable]
  -- the Brownian side
  have hright : ∫ ω, f (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω) ∂P'
      = ∫ x, g x ∂(Measure.pi fun j : Fin k ↦
          gaussianReal 0 (u ((j : ℕ) + 1) - u (j : ℕ)).toNNReal) := by
    have hpt : ∀ ω, f (fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω)
        = g fun j : Fin k ↦ B (u ((j : ℕ) + 1)) ω - B (u (j : ℕ)) ω := by
      intro ω
      rw [hgapp, ← bm_eq_cumSum hB.start_zero hu0 k ω]
    simp_rw [hpt]
    rw [← map_bmIncr_vector hB hu hu0' k,
      integral_map (measurable_pi_lambda _ fun j ↦
        ((hB.measurable _).sub (hB.measurable _))).aemeasurable
        g.continuous.aestronglyMeasurable]
  simp_rw [hleft, hright]
  refine tendsto_integral_pi_gaussian (fun j ↦ ?_) g
  rw [Real.coe_toNNReal _ (sub_nonneg.2 (hu (Nat.le_succ _)))]
  exact tendsto_walkIncrVar hu hu0' (j : ℕ)

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

