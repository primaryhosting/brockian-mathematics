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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/
noncomputable def cesaroAvg (x : ℕ → AddCircle (1 : ℝ)) (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)

section Basic

variable (x : ℕ → AddCircle (1 : ℝ))

lemma cesaroAvg_add (g₁ g₂ : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    cesaroAvg x (⇑(g₁ + g₂)) N = cesaroAvg x g₁ N + cesaroAvg x g₂ N := by
  simp only [cesaroAvg, ContinuousMap.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma cesaroAvg_sub (g₁ g₂ : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    cesaroAvg x (⇑(g₁ - g₂)) N = cesaroAvg x g₁ N - cesaroAvg x g₂ N := by
  simp only [cesaroAvg, ContinuousMap.coe_sub, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]

lemma cesaroAvg_smul (c : ℂ) (g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    cesaroAvg x (⇑(c • g)) N = c * cesaroAvg x g N := by
  simp only [cesaroAvg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma cesaroAvg_zero : cesaroAvg x (⇑(0 : C(AddCircle (1 : ℝ), ℂ))) = fun _ => 0 := by
  funext N; simp [cesaroAvg]

lemma cesaroAvg_fourier_zero {N : ℕ} (hN : 1 ≤ N) :
    cesaroAvg x (fourier (T := 1) 0) N = 1 := by
  have hne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [cesaroAvg, inv_mul_cancel₀ hne]

/-- The Cesàro averages are bounded by the sup-norm. -/
lemma norm_cesaroAvg_le (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖cesaroAvg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [cesaroAvg, h, norm_nonneg]
  · rw [cesaroAvg, norm_mul, norm_inv]
    have hN : (0 : ℝ) < N := by exact_mod_cast h
    have hsum : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum fun n _ => f.norm_coe_le_norm _
        _ = N * ‖f‖ := by simp
    have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [hcast, inv_mul_le_iff₀ hN]
    linarith

end Basic

/-- The `k`-th Fourier character integrates to zero over the circle for `k ≠ 0`. -/
lemma integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ t, (fourier k t : ℂ) ∂(haarAddCircle (T := 1)) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  rw [fourierCoeff] at h
  simpa [Pi.single, Function.update, hk, eq_comm] using h

/-- Continuous functions on the circle are integrable for the Haar probability measure. -/
lemma integrable_continuous (f : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable f (haarAddCircle (T := 1)) :=
  (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of a continuous function is bounded by its sup-norm. -/
lemma norm_integral_le (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖∫ t, f t ∂(haarAddCircle (T := 1))‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const (μ := haarAddCircle (T := 1)) (C := ‖f‖)
    (f := fun t => f t) (Filter.Eventually.of_forall fun t => f.norm_coe_le_norm t)

/-- Under the Weyl hypothesis, the Cesàro averages of every element of the span of the
Fourier characters converge to the corresponding integral. -/
lemma tendsto_cesaroAvg_of_mem_span (x : ℕ → AddCircle (1 : ℝ))
    (hx : ∀ k : ℤ, k ≠ 0 → Tendsto (cesaroAvg x (fourier k)) atTop (𝓝 0))
    (g : C(AddCircle (1 : ℝ), ℂ)) (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := 1)))) :
    Tendsto (cesaroAvg x g) atTop (𝓝 (∫ t, g t ∂(haarAddCircle (T := 1)))) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      rcases eq_or_ne k 0 with rfl | hk
      · have hint : ∫ t, (fourier (T := 1) 0 t : ℂ) ∂(haarAddCircle (T := 1)) = 1 := by simp
        rw [hint]
        refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)))
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact (cesaroAvg_fourier_zero x hN).symm
      · rw [integral_fourier_eq_zero hk]
        exact hx k hk
  | zero =>
      rw [cesaroAvg_zero]
      simp
  | add g₁ g₂ _ _ ih₁ ih₂ =>
      rw [show cesaroAvg x (⇑(g₁ + g₂)) = fun N => cesaroAvg x g₁ N + cesaroAvg x g₂ N from
        funext (cesaroAvg_add x g₁ g₂)]
      have hint : ∫ t, (g₁ + g₂) t ∂(haarAddCircle (T := 1))
          = (∫ t, g₁ t ∂(haarAddCircle (T := 1))) + ∫ t, g₂ t ∂(haarAddCircle (T := 1)) := by
        simp only [ContinuousMap.coe_add, Pi.add_apply]
        exact integral_add (integrable_continuous g₁) (integrable_continuous g₂)
      rw [hint]
      exact ih₁.add ih₂
  | smul c g _ ih =>
      rw [show cesaroAvg x (⇑(c • g)) = fun N => c * cesaroAvg x g N from
        funext (cesaroAvg_smul x c g)]
      have hint : ∫ t, (c • g) t ∂(haarAddCircle (T := 1))
          = c * ∫ t, g t ∂(haarAddCircle (T := 1)) := by
        simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact MeasureTheory.integral_const_mul c _
      rw [hint]
      exact ih.const_mul c

/-- Elements of the span of the Fourier characters are sup-norm dense in `C(ℝ/ℤ, ℂ)`. -/
lemma exists_mem_span_dist_lt (f : C(AddCircle (1 : ℝ), ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℂ (Set.range (fourier (T := 1))), dist f g < ε := by
  have hf : f ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := 1)))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  exact (Metric.mem_closure_iff.mp hf) ε hε

/-- **Weyl's equidistribution criterion.**  If the exponential sums
`(1/N) ∑_{n < N} e(k xₙ)` tend to `0` for every nonzero integer frequency `k`, then the
sequence `x` is equidistributed in the circle `ℝ/ℤ`: the Cesàro averages of every continuous
function converge to its integral against the Haar probability measure. -/
theorem equidistribution_of_asymptotic (x : ℕ → AddCircle (1 : ℝ))
    (hx : ∀ k : ℤ, k ≠ 0 → Tendsto (cesaroAvg x (fourier k)) atTop (𝓝 0))
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (cesaroAvg x f) atTop (𝓝 (∫ t, f t ∂(haarAddCircle (T := 1)))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hgdist⟩ := exists_mem_span_dist_lt f (by positivity : (0 : ℝ) < ε / 3)
  have hg := tendsto_cesaroAvg_of_mem_span x hx g hgmem
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N₀, hN₀⟩ := hg (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖cesaroAvg x f N - cesaroAvg x g N‖ < ε / 3 := by
    rw [← cesaroAvg_sub]
    exact lt_of_le_of_lt (norm_cesaroAvg_le x (f - g) N) (by
      rwa [← NormedAddGroup.dist_eq])
  have h2 : dist (cesaroAvg x g N) (∫ t, g t ∂(haarAddCircle (T := 1))) < ε / 3 := hN₀ N hN
  have h3 : ‖(∫ t, g t ∂(haarAddCircle (T := 1))) - ∫ t, f t ∂(haarAddCircle (T := 1))‖
      < ε / 3 := by
    rw [← integral_sub (integrable_continuous g) (integrable_continuous f)]
    refine lt_of_le_of_lt ?_ (by rwa [← NormedAddGroup.dist_eq, dist_comm] :
      ‖g - f‖ < ε / 3)
    simpa using norm_integral_le (g - f)
  calc dist (cesaroAvg x f N) (∫ t, f t ∂(haarAddCircle (T := 1)))
      ≤ dist (cesaroAvg x f N) (cesaroAvg x g N)
        + dist (cesaroAvg x g N) (∫ t, g t ∂(haarAddCircle (T := 1)))
        + dist (∫ t, g t ∂(haarAddCircle (T := 1))) (∫ t, f t ∂(haarAddCircle (T := 1))) := by
        exact dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_eq_norm, dist_eq_norm (∫ t, g t ∂(haarAddCircle (T := 1)))]
        exact add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring

/-!
### An unconditional application: irrational rotations

The hypothesis of `equidistribution_of_asymptotic` is verified for the orbit `n ↦ n * a`
of an irrational rotation, which yields Weyl's equidistribution theorem for `(n a)` unconditionally.
-/

/-- For irrational `a` and a nonzero frequency `k`, the exponential sums along the orbit
`n ↦ n * a` of the irrational rotation tend to zero (geometric sum bound). -/
theorem tendsto_cesaroAvg_fourier_irrational {a : ℝ} (ha : Irrational a) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) (fourier k)) atTop
      (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * a) with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    rw [hzdef, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (k : ℂ) * (a : ℂ) = (m : ℂ) := by
      have h4 : (2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * a)
          = (2 * (Real.pi : ℂ) * Complex.I) * m := by linear_combination hm
      exact mul_left_cancel₀ (by simp [hpi, Complex.I_ne_zero]) h4
    exact (ha.intCast_mul hk).ne_int m (by exact_mod_cast h2)
  have hznorm : ‖z‖ = 1 := by rw [hzdef, Complex.norm_exp]; norm_num
  have hterm : ∀ n : ℕ, fourier (T := 1) k ((n * a : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
    intro n
    rw [fourier_coe_apply, hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz0 : (0 : ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  have hbound : ∀ N : ℕ, ‖cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) (fourier k) N‖
      ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    intro N
    have hEq : cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) (fourier k) N
        = (N : ℂ)⁻¹ * ((z ^ N - 1) / (z - 1)) := by
      rw [cesaroAvg]
      simp only [hterm]
      rw [geom_sum_eq hz1]
    rw [hEq, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have h1 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    gcongr
  refine squeeze_zero_norm' (Eventually.of_forall hbound) ?_
  simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.mul_const (2 / ‖z - 1‖)

/-- **Weyl's equidistribution theorem for irrational rotations.**  For irrational `a`, the
sequence `n ↦ n * a` is equidistributed in `ℝ/ℤ`: the Cesàro averages of every continuous
function converge to its integral against the Haar probability measure. -/
theorem equidistribution_irrational {a : ℝ} (ha : Irrational a) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (cesaroAvg (fun n : ℕ => ((n * a : ℝ) : AddCircle (1 : ℝ))) f) atTop
      (𝓝 (∫ t, f t ∂(haarAddCircle (T := 1)))) :=
  equidistribution_of_asymptotic _ (fun _ hk => tendsto_cesaroAvg_fourier_irrational ha hk) f

end Brockian.Equidistribution

