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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution: existence of the asymptotic average

This file develops Weyl's criterion for equidistribution modulo one on the circle
`AddCircle (1 : ℝ) = ℝ / ℤ`, and deduces from it Weyl's equidistribution theorem for the
sequence `n ↦ n * a` with `a` irrational.

Main results:

* `Brockian.Equidistribution.isEquidistributed_of_tendsto_fourier`: Weyl's criterion.
* `Brockian.Equidistribution.isEquidistributed_irrational`: the orbit of an irrational
  rotation is equidistributed mod 1.
* `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`: unconditional statement
  that for irrational `a` the asymptotic average of any continuous function along `n * a`
  exists and equals the integral of the function.
-/

open MeasureTheory Filter Complex
open scoped Topology BigOperators

namespace Brockian.Equidistribution

local instance factZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The Birkhoff-type average of a continuous function `f` on the circle `ℝ / ℤ` along the
first `N` points of the real sequence `x`, taken modulo `1`. -/
noncomputable def avg (x : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : AddCircle (1 : ℝ))

/-- A real sequence is *equidistributed mod 1* if the averages of every continuous function on
the circle along the sequence converge to the integral of that function with respect to the
Haar probability measure. -/
def IsEquidistributed (x : ℕ → ℝ) : Prop :=
  ∀ f : C(AddCircle (1 : ℝ), ℂ),
    Tendsto (avg x f) atTop (𝓝 (∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle))

section Basic

variable (x : ℕ → ℝ)

lemma avg_sub (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    avg x (f - g) N = avg x f N - avg x g N := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

lemma norm_avg_le (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ‖avg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [avg]
  · rw [avg, norm_mul]
    have h1 : ‖∑ n ∈ Finset.range N, f ((x n : ℝ) : AddCircle (1 : ℝ))‖ ≤ N * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f ((x n : ℝ) : AddCircle (1 : ℝ))‖
          ≤ ∑ n ∈ Finset.range N, ‖f ((x n : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum fun n _ => f.norm_coe_le_norm _
        _ = N * ‖f‖ := by simp
    have h2 : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
    rw [h2, inv_mul_le_iff₀ (by positivity)]
    exact h1

lemma integrable_circle (f : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable f (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma norm_integral_le (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (f := fun t => f t) (C := ‖f‖)
    (Filter.Eventually.of_forall fun t => f.norm_coe_le_norm t)

end Basic

/-- The integral of the character `fourier k` over the circle: it vanishes unless `k = 0`. -/
lemma integral_fourier (k : ℤ) :
    ∫ t : AddCircle (1 : ℝ), (fourier k) t ∂AddCircle.haarAddCircle = if k = 0 then 1 else 0 := by
  have h0 := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simp only [fourierCoeff, Pi.single_apply, fourier_zero, neg_zero, one_smul] at h0
  simp only [fourier_apply] at h0 ⊢
  simpa [eq_comm] using h0

/-- **Weyl's criterion.** If all the nontrivial character averages of a sequence tend to zero,
then the sequence is equidistributed mod 1. -/
theorem isEquidistributed_of_tendsto_fourier (x : ℕ → ℝ)
    (h : ∀ k : ℤ, k ≠ 0 → Tendsto (avg x (fourier k)) atTop (𝓝 0)) :
    IsEquidistributed x := by
  set S : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
  { carrier := {f | Tendsto (avg x f) atTop
        (𝓝 (∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle))}
    add_mem' := by
      intro f g hf hg
      simp only [Set.mem_setOf_eq, ContinuousMap.add_apply] at *
      have hav : avg x (f + g) = fun N => avg x f N + avg x g N := by
        funext N; simp [avg, Finset.sum_add_distrib, mul_add]
      rw [integral_add (integrable_circle f) (integrable_circle g), hav]
      exact hf.add hg
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      have hav : avg x 0 = fun _ => (0 : ℂ) := by funext N; simp [avg]
      rw [hav]; simp
    smul_mem' := by
      intro c f hf
      simp only [Set.mem_setOf_eq, ContinuousMap.smul_apply, smul_eq_mul] at *
      have hav : avg x (c • f) = fun N => c * avg x f N := by
        funext N
        simp only [avg, ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [integral_const_mul, hav]
      exact hf.const_mul c } with hS
  have hmemS : ∀ f : C(AddCircle (1 : ℝ), ℂ), f ∈ S ↔ Tendsto (avg x f) atTop
      (𝓝 (∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle)) := fun f => Iff.rfl
  -- `S` is closed, by a `3ε`-argument using that averages and integrals are contractions
  -- for the uniform norm.
  have hclosed : IsClosed (S : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← closure_subset_iff_isClosed]
    intro f hf
    rw [SetLike.mem_coe, hmemS, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 3) (by linarith)
    rw [SetLike.mem_coe, hmemS, Metric.tendsto_atTop] at hgS
    obtain ⟨N₀, hN₀⟩ := hgS (ε / 3) (by linarith)
    refine ⟨N₀, fun N hN => ?_⟩
    have hnorm : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
    have h1 : ‖avg x f N - avg x g N‖ < ε / 3 := by
      rw [← avg_sub]; exact lt_of_le_of_lt (norm_avg_le x _ N) hnorm
    have h2 : dist (avg x g N) (∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle) < ε / 3 :=
      hN₀ N hN
    have h3 : ‖(∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
        - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ < ε / 3 := by
      rw [← integral_sub (integrable_circle g) (integrable_circle f)]
      have hgf : ∀ t : AddCircle (1 : ℝ), g t - f t = (g - f) t := fun t => rfl
      simp only [hgf]
      calc ‖∫ t : AddCircle (1 : ℝ), (g - f) t ∂AddCircle.haarAddCircle‖ ≤ ‖g - f‖ :=
            norm_integral_le _
        _ = ‖f - g‖ := by rw [norm_sub_rev]
        _ < ε / 3 := hnorm
    rw [dist_eq_norm] at h2 ⊢
    calc ‖avg x f N - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖
        = ‖(avg x f N - avg x g N)
            + (avg x g N - ∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
            + ((∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
              - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle)‖ := by ring_nf
      _ ≤ ‖(avg x f N - avg x g N)
            + (avg x g N - ∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)‖
            + ‖(∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
              - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ := norm_add_le _ _
      _ ≤ ‖avg x f N - avg x g N‖
            + ‖avg x g N - ∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle‖
            + ‖(∫ t : AddCircle (1 : ℝ), g t ∂AddCircle.haarAddCircle)
              - ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle‖ := by
            gcongr; exact norm_add_le _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
      _ = ε := by ring
  -- the characters belong to `S`
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hmemS, integral_fourier]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl]
      have hav : ∀ N : ℕ, 1 ≤ N → avg x (fourier (T := (1 : ℝ)) 0) N = 1 := by
        intro N hN
        simp only [avg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [inv_mul_cancel₀]
        exact Nat.cast_ne_zero.mpr (by omega)
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop 1] with N hN using (hav N hN).symm
    · simpa [if_neg hk] using h k hk
  -- the characters span a dense subspace, so `S = ⊤`
  intro f
  have hf : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  have hf3 : f ∈ closure (S : Set C(AddCircle (1 : ℝ), ℂ)) :=
    closure_mono (by exact_mod_cast hspan) hf
  rw [hclosed.closure_eq] at hf3
  exact (hmemS f).1 hf3

/-- For irrational `a` and `k ≠ 0`, the complex number `exp (2 π i k a)` is not equal to `1`. -/
lemma exp_two_pi_I_ne_one {a : ℝ} (ha : Irrational a) {k : ℤ} (hk : k ≠ 0) :
    Complex.exp (2 * Real.pi * I * k * a) ≠ 1 := by
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨m, hm⟩ := hcon
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : (2 * (Real.pi : ℂ) * I) * ((k : ℂ) * a - m) = 0 := by
    ring_nf; ring_nf at hm; linear_combination hm
  have h3 : (k : ℂ) * a - m = 0 := by
    rcases mul_eq_zero.1 h2 with h4 | h4
    · exact absurd h4 (by simp [hpi, hI])
    · exact h4
  have h5 : (k : ℂ) * a = m := by linear_combination h3
  have h6 : (k : ℝ) * a = m := by exact_mod_cast h5
  exact (ha.intCast_mul hk).ne_int m h6

/-- The character averages of the orbit of an irrational rotation tend to zero. -/
lemma tendsto_avg_fourier_irrational {a : ℝ} (ha : Irrational a) (k : ℤ) (hk : k ≠ 0) :
    Tendsto (avg (fun n : ℕ => (n : ℝ) * a) (fourier k)) atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * I * k * a) with hz
  have hzn : ∀ n : ℕ, (fourier k) (((n : ℝ) * a : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
    intro n
    rw [fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzabs : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    simp [Complex.re_ofNat]
  have hzne : z ≠ 1 := exp_two_pi_I_ne_one ha hk
  have hsub : ‖z - 1‖ > 0 := by simpa [sub_eq_zero] using hzne
  refine squeeze_zero_norm (a := fun N : ℕ => (N : ℝ)⁻¹ * (2 / ‖z - 1‖)) (fun N => ?_) ?_
  · have hsum : ∑ n ∈ Finset.range N, (fourier k) (((n : ℝ) * a : ℝ) : AddCircle (1 : ℝ))
        = (z ^ N - 1) / (z - 1) := by
      rw [Finset.sum_congr rfl fun n _ => hzn n, geom_sum_eq hzne]
    rw [avg]
    simp only [hsum, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hzabs]; norm_num
    have hdiv : ‖z ^ N - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ := by gcongr
    exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using h1.mul_const (2 / ‖z - 1‖)

/-- **Weyl's equidistribution theorem**: for irrational `a`, the sequence `n ↦ n * a` is
equidistributed mod 1. -/
theorem isEquidistributed_irrational {a : ℝ} (ha : Irrational a) :
    IsEquidistributed (fun n : ℕ => (n : ℝ) * a) :=
  isEquidistributed_of_tendsto_fourier _ (tendsto_avg_fourier_irrational ha)

/-- For an irrational `a` and any continuous function `f` on the circle, the asymptotic average
of `f` along the orbit `n ↦ n * a` exists, and its value is the integral of `f` against the Haar
probability measure: the sequence `n * a` is equidistributed mod 1. -/
theorem equidistribution_of_asymptotic_exists {a : ℝ} (ha : Irrational a) :
    ∀ f : C(AddCircle (1 : ℝ), ℂ), ∃ L : ℂ,
      Tendsto (avg (fun n : ℕ => (n : ℝ) * a) f) atTop (𝓝 L) ∧
        L = ∫ t : AddCircle (1 : ℝ), f t ∂AddCircle.haarAddCircle :=
  fun f => ⟨_, isEquidistributed_irrational ha f, rfl⟩

end Brockian.Equidistribution

