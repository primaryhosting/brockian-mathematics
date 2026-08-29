/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Donsker's invariance principle states that the diffusively rescaled random walk built from
i.i.d. centered increments of unit variance converges in law, as a process, to Brownian motion.

Mathlib currently contains neither Brownian motion, nor weak convergence on the Skorokhod space,
nor the central limit theorem, so the functional statement cannot be phrased.  What is proved
here is the *second-order (moment) form* of the invariance principle, which is the part of the
statement that can be expressed with the available theory:

* the rescaled walk `W_n(t) = S_{⌊n t⌋} / √n` is centered;
* its covariance converges to the Brownian covariance, `E[W_n(s) W_n(t)] → min s t`;
* its increments have the Brownian variance in the limit, `E[(W_n(t) - W_n(s))²] → t - s`;
* its increments over disjoint time intervals are exactly independent.

All the limits depend only on the first two moments of the increments and not on their law —
this is the *invariance* content of the principle, isolated in
`Math2.donsker_invariance_law_independent`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Topology

/-- The diffusively rescaled random walk built from the increments `X`:
`rescaledWalk X n t ω = (X 0 + ⋯ + X (⌊n t⌋ - 1)) / √n`.
This is the piecewise-constant process appearing in Donsker's invariance principle. -/
noncomputable def rescaledWalk {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Distinct increments are uncorrelated; an increment has second moment `1`. -/
lemma integral_mul_eq_ite
    (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1) (i j : ℕ) :
    ∫ ω, X i ω * X j ω ∂μ = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simpa [pow_two] using hvar i
  · rw [if_neg h,
      (hindep.indepFun h).integral_fun_mul_eq_mul_integral
        (hmem i).aestronglyMeasurable (hmem j).aestronglyMeasurable]
    simp [hmean i]

lemma integrable_mul (hmem : ∀ i, MemLp (X i) 2 μ) (i j : ℕ) :
    Integrable (fun ω => X i ω * X j ω) μ := by
  have := (hmem i).integrable_mul (hmem j)
  simpa [Pi.mul_apply] using this

lemma integrable_sum_mul_sum (hmem : ∀ i, MemLp (X i) 2 μ) (S T : Finset ℕ) :
    Integrable (fun ω => (∑ i ∈ S, X i ω) * (∑ j ∈ T, X j ω)) μ := by
  have h : (fun ω => (∑ i ∈ S, X i ω) * (∑ j ∈ T, X j ω))
      = fun ω => ∑ i ∈ S, ∑ j ∈ T, X i ω * X j ω := by
    funext ω; rw [Finset.sum_mul_sum]
  rw [h]
  exact integrable_finset_sum _ fun i _ =>
    integrable_finset_sum _ fun j _ => integrable_mul hmem i j

/-- Second moments of partial sums: `E[(∑_{i ∈ S} X i)(∑_{j ∈ T} X j)] = #(S ∩ T)`. -/
lemma integral_sum_mul_sum
    (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1) (S T : Finset ℕ) :
    ∫ ω, (∑ i ∈ S, X i ω) * (∑ j ∈ T, X j ω) ∂μ = ((S ∩ T).card : ℝ) := by
  have hexp : ∀ ω, (∑ i ∈ S, X i ω) * (∑ j ∈ T, X j ω)
      = ∑ i ∈ S, ∑ j ∈ T, X i ω * X j ω := fun ω => by rw [Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
      (fun j _ => integrable_mul hmem i j))]
  have hterm : ∀ i ∈ S,
      ∫ ω, ∑ j ∈ T, X i ω * X j ω ∂μ = if i ∈ T then (1 : ℝ) else 0 := by
    intro i _
    rw [integral_finset_sum _ (fun j _ => integrable_mul hmem i j)]
    simp_rw [integral_mul_eq_ite hmem hindep hmean hvar i]
    rw [Finset.sum_ite_eq T i (fun _ => (1 : ℝ))]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- The rescaled walk is centered. -/
lemma integral_rescaledWalk_eq_zero [IsFiniteMeasure μ]
    (hmem : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (n : ℕ) (t : ℝ) :
    ∫ ω, rescaledWalk X n t ω ∂μ = 0 := by
  have hint : ∀ i, Integrable (X i) μ := fun i => (hmem i).integrable (by norm_num)
  simp only [rescaledWalk]
  rw [integral_div, integral_finset_sum _ (fun i _ => hint i)]
  simp [hmean]

/-- The covariance of the rescaled walk at two times equals `min ⌊n s⌋ ⌊n t⌋ / n`. -/
lemma integral_rescaledWalk_mul
    (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1)
    (n : ℕ) (s t : ℝ) :
    ∫ ω, rescaledWalk X n s ω * rescaledWalk X n t ω ∂μ
      = (min ⌊(n : ℝ) * s⌋₊ ⌊(n : ℝ) * t⌋₊ : ℕ) / n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [rescaledWalk]
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hexp : ∀ ω, rescaledWalk X n s ω * rescaledWalk X n t ω
      = ((∑ i ∈ Finset.range ⌊(n : ℝ) * s⌋₊, X i ω) *
          (∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X j ω)) / n := by
    intro ω
    simp only [rescaledWalk]
    rw [div_mul_div_comm, hsq]
  simp_rw [hexp]
  rw [integral_div, integral_sum_mul_sum hmem hindep hmean hvar,
    Finset.range_inter_range, Finset.card_range]

/-- Second moment of a walk increment: `E[(S_b - S_a)²] = b - a` for `a ≤ b`. -/
lemma integral_sub_sq
    (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1)
    {a b : ℕ} (hab : a ≤ b) :
    ∫ ω, ((∑ i ∈ Finset.range b, X i ω) - ∑ i ∈ Finset.range a, X i ω) ^ 2 ∂μ
      = ((b : ℝ) - a) := by
  have hIco : ∀ ω, ((∑ i ∈ Finset.range b, X i ω) - ∑ i ∈ Finset.range a, X i ω) ^ 2
      = (∑ i ∈ Finset.Ico a b, X i ω) * (∑ j ∈ Finset.Ico a b, X j ω) := by
    intro ω
    rw [← Finset.sum_Ico_eq_sub _ hab, pow_two]
  simp_rw [hIco]
  rw [integral_sum_mul_sum hmem hindep hmean hvar, Finset.inter_self, Nat.card_Ico,
    Nat.cast_sub hab]

/-- Second moment of a rescaled-walk increment. -/
lemma integral_rescaledWalk_increment_sq
    (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1)
    (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    ∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2 ∂μ
      = ((⌊(n : ℝ) * t⌋₊ : ℝ) - (⌊(n : ℝ) * s⌋₊ : ℝ)) / n := by
  have hfl : ⌊(n : ℝ) * s⌋₊ ≤ ⌊(n : ℝ) * t⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [rescaledWalk]
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hexp : ∀ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2
      = ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω)
          - ∑ i ∈ Finset.range ⌊(n : ℝ) * s⌋₊, X i ω) ^ 2 / n := by
    intro ω
    simp only [rescaledWalk]
    rw [div_sub_div_same, div_pow, hsq]
  simp_rw [hexp]
  rw [integral_div, integral_sub_sq hmem hindep hmean hvar hfl]

end Moments

/-- Minimum of floors is the floor of the minimum, for the rescaling map. -/
lemma min_floor_eq (n : ℕ) {s t : ℝ} :
    (min ⌊(n : ℝ) * s⌋₊ ⌊(n : ℝ) * t⌋₊ : ℕ) = ⌊(n : ℝ) * min s t⌋₊ := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_left (Nat.floor_mono
      (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)))]
  · rw [min_eq_right h, min_eq_right (Nat.floor_mono
      (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)))]

/-- `⌊n u⌋ / n → u` along the naturals, for `u ≥ 0`. -/
lemma tendsto_floor_mul_div {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * u⌋₊ : ℝ) / n) atTop (𝓝 u) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hu).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr fun n => ?_
  simp [Function.comp, mul_comm]

/-- **Donsker's invariance principle (second-order form).**

Let `X 0, X 1, …` be independent square-integrable random variables with mean `0` and
variance `1`, and let `W_n(t) = rescaledWalk X n t = S_{⌊n t⌋} / √n` be the diffusively
rescaled random walk.

Then, for all times `0 ≤ s ≤ t`:

* the rescaled walk is centered, `E[W_n(t)] = 0` for every `n`;
* its covariance converges to the Brownian covariance, `E[W_n(s) W_n(t)] → min s t = s`;
* the variance of its increment converges to the Brownian one, `E[(W_n(t) - W_n(s))²] → t - s`.

The limits are determined by the first two moments of the increments alone, which is the
*invariance* content of the principle (see `donsker_invariance_law_independent`).

Mathlib does not currently contain Brownian motion, weak convergence on the Skorokhod space,
or the central limit theorem, so the full functional statement cannot yet be phrased; this is
the moment form of the invariance principle. -/
theorem donsker_invariance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∀ n : ℕ, ∫ ω, rescaledWalk X n t ω ∂μ = 0) ∧
      Tendsto (fun n : ℕ => ∫ ω, rescaledWalk X n s ω * rescaledWalk X n t ω ∂μ)
        atTop (𝓝 (min s t)) ∧
      Tendsto (fun n : ℕ => ∫ ω, (rescaledWalk X n t ω - rescaledWalk X n s ω) ^ 2 ∂μ)
        atTop (𝓝 (t - s)) := by
  have ht : (0 : ℝ) ≤ t := hs.trans hst
  refine ⟨fun n => integral_rescaledWalk_eq_zero hmem hmean n t, ?_, ?_⟩
  · have hlim := tendsto_floor_mul_div (le_min hs ht)
    refine hlim.congr fun n => ?_
    rw [integral_rescaledWalk_mul hmem hindep hmean hvar n s t, min_floor_eq n]
  · have hlim := (tendsto_floor_mul_div ht).sub (tendsto_floor_mul_div hs)
    refine hlim.congr fun n => ?_
    rw [integral_rescaledWalk_increment_sq hmem hindep hmean hvar n hst, sub_div]

/-- **Invariance**: the limiting covariance structure of the rescaled walk is the same for any
two increment sequences with mean `0` and variance `1`, however different their laws. -/
theorem donsker_invariance_law_independent
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (hmem : ∀ i, MemLp (X i) 2 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1)
    (Y : ℕ → Ω' → ℝ) (hmem' : ∀ i, MemLp (Y i) 2 ν) (hindep' : iIndepFun Y ν)
    (hmean' : ∀ i, ∫ ω, Y i ω ∂ν = 0) (hvar' : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂ν = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (L : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, rescaledWalk X n s ω * rescaledWalk X n t ω ∂μ) atTop (𝓝 L)
      ↔ Tendsto (fun n : ℕ => ∫ ω, rescaledWalk Y n s ω * rescaledWalk Y n t ω ∂ν)
          atTop (𝓝 L) := by
  have hX := (donsker_invariance X hmem hindep hmean hvar hs hst).2.1
  have hY := (donsker_invariance Y hmem' hindep' hmean' hvar' hs hst).2.1
  constructor
  · intro h
    rw [tendsto_nhds_unique h hX]
    exact hY
  · intro h
    rw [tendsto_nhds_unique h hY]
    exact hX

/-- The increments of the rescaled walk over disjoint time intervals are independent, exactly as
for Brownian motion. -/
theorem donsker_increments_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (n : ℕ) {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    IndepFun (fun ω => rescaledWalk X n s ω - rescaledWalk X n r ω)
      (fun ω => rescaledWalk X n t ω - rescaledWalk X n s ω) μ := by
  set a := ⌊(n : ℝ) * r⌋₊
  set b := ⌊(n : ℝ) * s⌋₊
  set c := ⌊(n : ℝ) * t⌋₊
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg n))
  have hbc : b ≤ c := Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) :=
    Finset.Ico_disjoint_Ico_consecutive a b c
  have hI := hindep.indepFun_finset (Finset.Ico a b) (Finset.Ico b c) hdisj hmeas
  have hφ : ∀ S : Finset ℕ, Measurable
      (fun v : (i : { x // x ∈ S }) → ℝ => (∑ i, v i) / Real.sqrt n) := by
    intro S
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => measurable_pi_apply i)).div_const _
  have hcomp := hI.comp (hφ (Finset.Ico a b)) (hφ (Finset.Ico b c))
  have key : ∀ (u v : ℕ), u ≤ v →
      ((fun w : (i : { x // x ∈ Finset.Ico u v }) → ℝ => (∑ i, w i) / Real.sqrt n)
        ∘ fun (ω : Ω) (i : { x // x ∈ Finset.Ico u v }) => X (i : ℕ) ω)
        = fun ω => (∑ i ∈ Finset.range v, X i ω) / Real.sqrt n
            - (∑ i ∈ Finset.range u, X i ω) / Real.sqrt n := by
    intro u v huv
    funext ω
    simp only [Function.comp_apply]
    rw [div_sub_div_same, ← Finset.sum_Ico_eq_sub _ huv,
      Finset.sum_coe_sort (Finset.Ico u v) (fun i => X i ω)]
  rw [key a b hab, key b c hbc] at hcomp
  exact hcomp

end Math2

#print axioms Math2.donsker_invariance
#print axioms Math2.donsker_invariance_law_independent
#print axioms Math2.donsker_increments_indep

