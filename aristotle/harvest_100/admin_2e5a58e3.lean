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

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open Filter MeasureTheory AddCircle

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Cesàro average of `f` along the first `N` terms of the sequence `u`. -/
noncomputable def avg (u : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n)

omit hT in
lemma avg_add (u : ℕ → AddCircle T) (f g : C(AddCircle T, ℂ)) (N : ℕ) :
    avg u (f + g) N = avg u f N + avg u g N := by
  simp [avg, Finset.sum_add_distrib, mul_add]

omit hT in
lemma avg_smul (u : ℕ → AddCircle T) (c : ℂ) (f : C(AddCircle T, ℂ)) (N : ℕ) :
    avg u (c • f) N = c * avg u f N := by
  simp only [avg, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

omit hT in
lemma avg_sub (u : ℕ → AddCircle T) (f g : C(AddCircle T, ℂ)) (N : ℕ) :
    avg u (f - g) N = avg u f N - avg u g N := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

lemma norm_avg_le (u : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) {N : ℕ} (hN : 1 ≤ N) :
    ‖avg u f N‖ ≤ ‖f‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hsum : ‖∑ n ∈ Finset.range N, f (u n)‖ ≤ N * ‖f‖ := by
    calc ‖∑ n ∈ Finset.range N, f (u n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (u n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ :=
          Finset.sum_le_sum fun n _ => f.norm_coe_le_norm (u n)
      _ = N * ‖f‖ := by simp
  have : ‖avg u f N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f (u n)‖ := by
    simp [avg]
  rw [this]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f (u n)‖ ≤ (N : ℝ)⁻¹ * (N * ‖f‖) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖f‖ := by field_simp

lemma integrable_contMap (f : C(AddCircle T, ℂ)) :
    Integrable (fun x => f x) (@haarAddCircle T hT) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma norm_integral_le (f : C(AddCircle T, ℂ)) :
    ‖∫ x, f x ∂(@haarAddCircle T hT)‖ ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := (@haarAddCircle T hT)) (C := ‖f‖)
    (f := fun x => f x) (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
  simpa using this

lemma integral_fourier_ne_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ x, (fourier m x : ℂ) ∂(@haarAddCircle T hT) = 0 :=
  MeasureTheory.integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
    (fourier_add_half_inv_index hm hT.elim)

/-- The conclusion holds for every element of the span of the Fourier monomials. -/
lemma tendsto_of_mem_span (u : ℕ → AddCircle T)
    (hu : ∀ m : ℤ, m ≠ 0 → Tendsto (avg u (fourier m)) atTop (nhds 0))
    (f : C(AddCircle T, ℂ)) (hf : f ∈ Submodule.span ℂ (Set.range (@fourier T))) :
    Tendsto (avg u f) atTop (nhds (∫ x, f x ∂(@haarAddCircle T hT))) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨m, rfl⟩ := hg
      rcases eq_or_ne m 0 with rfl | hm
      · have hint : ∫ x, (fourier (0 : ℤ) x : ℂ) ∂(@haarAddCircle T hT) = 1 := by
          simp
        rw [hint]
        have heq : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop] avg u (fourier (0 : ℤ)) := by
          filter_upwards [eventually_ge_atTop 1] with N hN
          have hN0 : (N : ℂ) ≠ 0 := by
            simpa using (Nat.pos_of_ne_zero (by omega) : 0 < N).ne'
          simp [avg, hN0]
        exact Tendsto.congr' heq tendsto_const_nhds
      · rw [integral_fourier_ne_zero hm]
        exact hu m hm
  | zero =>
      have h0 : avg u (0 : C(AddCircle T, ℂ)) = fun _ : ℕ => (0 : ℂ) := by
        funext N; simp [avg]
      rw [h0]
      simp only [ContinuousMap.zero_apply, integral_zero]
      exact tendsto_const_nhds
  | add g h _ _ ihg ihh =>
      have hint : ∫ x, ((g + h) x : ℂ) ∂(@haarAddCircle T hT)
          = (∫ x, g x ∂(@haarAddCircle T hT)) + ∫ x, h x ∂(@haarAddCircle T hT) := by
        simpa using integral_add (integrable_contMap g) (integrable_contMap h)
      rw [hint, funext (avg_add u g h)]
      exact ihg.add ihh
  | smul c g _ ih =>
      have hint : ∫ x, ((c • g) x : ℂ) ∂(@haarAddCircle T hT)
          = c * ∫ x, g x ∂(@haarAddCircle T hT) := by
        simpa [smul_eq_mul] using integral_smul c (fun x => g x) (μ := (@haarAddCircle T hT))
      rw [hint, funext (avg_smul u c g)]
      exact ih.const_mul c

/-- **Weyl's equidistribution criterion.**  If, for every nonzero frequency `m`, the Cesàro
averages of the character `fourier m` along the sequence `u : ℕ → AddCircle T` tend to `0`,
then the sequence is equidistributed: for every continuous `f : AddCircle T → ℂ`, the Cesàro
averages of `f` along `u` converge to the mean value of `f` with respect to normalized Haar
measure. -/
theorem equidistribution_of_asymptotic (u : ℕ → AddCircle T)
    (hu : ∀ m : ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (u n)) atTop (nhds 0))
    (f : C(AddCircle T, ℂ)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n)) atTop
      (nhds (∫ x, f x ∂(@haarAddCircle T hT))) := by
  have hu' : ∀ m : ℤ, m ≠ 0 → Tendsto (avg u (fourier m)) atTop (nhds 0) := hu
  show Tendsto (avg u f) atTop (nhds (∫ x, f x ∂(@haarAddCircle T hT)))
  -- `f` lies in the closure of the span of the Fourier monomials
  have hdense : f ∈ closure ((Submodule.span ℂ (Set.range (@fourier T)) : Submodule ℂ _) :
      Set C(AddCircle T, ℂ)) := by
    have h := @span_fourier_closure_eq_top T _
    have : f ∈ (Submodule.span ℂ (Set.range (@fourier T))).topologicalClosure := by
      rw [h]; trivial
    simpa [Submodule.topologicalClosure_coe] using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hfg⟩ := Metric.mem_closure_iff.1 hdense (ε / 3) (by linarith)
  have hgtend := tendsto_of_mem_span u hu' g hgmem
  rw [Metric.tendsto_atTop] at hgtend
  obtain ⟨N₁, hN₁⟩ := hgtend (ε / 3) (by linarith)
  refine ⟨max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hnorm : ‖f - g‖ < ε / 3 := by
    have : dist f g < ε / 3 := hfg
    rwa [dist_eq_norm] at this
  have h1 : dist (avg u f N) (avg u g N) < ε / 3 := by
    rw [dist_eq_norm, ← avg_sub]
    exact lt_of_le_of_lt (norm_avg_le u (f - g) hN1) hnorm
  have h2 : dist (avg u g N) (∫ x, g x ∂(@haarAddCircle T hT)) < ε / 3 := hN₁ N hNN₁
  have h3 : dist (∫ x, g x ∂(@haarAddCircle T hT)) (∫ x, f x ∂(@haarAddCircle T hT)) < ε / 3 := by
    have hsub : (∫ x, f x ∂(@haarAddCircle T hT)) - ∫ x, g x ∂(@haarAddCircle T hT)
        = ∫ x, ((f - g) x : ℂ) ∂(@haarAddCircle T hT) := by
      simpa using (integral_sub (integrable_contMap f) (integrable_contMap g)).symm
    rw [dist_comm, dist_eq_norm, hsub]
    exact lt_of_le_of_lt (norm_integral_le (f - g)) hnorm
  calc dist (avg u f N) (∫ x, f x ∂(@haarAddCircle T hT))
      ≤ dist (avg u f N) (avg u g N) + dist (avg u g N) (∫ x, g x ∂(@haarAddCircle T hT))
        + dist (∫ x, g x ∂(@haarAddCircle T hT)) (∫ x, f x ∂(@haarAddCircle T hT)) := by
        exact dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- Real-valued form of Weyl's criterion: under the same hypothesis, the Cesàro averages of any
continuous real-valued function along `u` converge to its mean value. -/
theorem equidistribution_of_asymptotic_real (u : ℕ → AddCircle T)
    (hu : ∀ m : ℤ, m ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier m (u n)) atTop (nhds 0))
    (f : C(AddCircle T, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (u n)) atTop
      (nhds (∫ x, f x ∂(@haarAddCircle T hT))) := by
  set F : C(AddCircle T, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
    with hF
  have hmain := equidistribution_of_asymptotic u hu F
  have hint : ∫ x, F x ∂(@haarAddCircle T hT) = ((∫ x, f x ∂(@haarAddCircle T hT) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hcast : ∀ N : ℕ, (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, F (u n)
      = (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (u n) : ℝ) : ℂ) := by
    intro N
    push_cast [hF]
    rfl
  rw [hint] at hmain
  simp only [hcast] at hmain
  exact tendsto_ofReal_iff.mp hmain

end Brockian.Equidistribution

