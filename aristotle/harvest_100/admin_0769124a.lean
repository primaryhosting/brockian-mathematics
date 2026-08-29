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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian.Equidistribution

open Filter MeasureTheory Set Submodule
open scoped Topology BigOperators

/-- The number of indices `n < N` for which the fractional part of `u n` lies in `[a, b)`. -/
noncomputable def countIco (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (u n) ∈ Set.Ico a b)).card

/-- A real sequence is equidistributed mod 1 if, for every subinterval `[a, b)` of `[0, 1]`,
the asymptotic frequency with which the fractional parts of the sequence visit `[a, b)`
exists and equals the length `b - a`. -/
def EquidistributedMod1 (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (countIco u a b N : ℝ) / N) atTop (𝓝 (b - a))

/-- The `k`-th Weyl (exponential) sum of the sequence `u`, truncated at `N`. -/
noncomputable def weylSum (u : ℕ → ℝ) (k : ℤ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * u n)

/-- The asymptotic (Weyl) hypothesis: all nonzero Weyl sums are `o(N)`. -/
def WeylVanishing (u : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => weylSum u k N / N) atTop (𝓝 0)

/-- Cesàro averages of a continuous function on the circle along the sequence `u`. -/
noncomputable def circleAvg (u : ℕ → ℝ) (f : C(UnitAddCircle, ℂ)) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, f (u n : UnitAddCircle)) / N

lemma integrable_continuousMap (f : C(UnitAddCircle, ℂ)) :
    Integrable (fun x => f x) (volume : Measure UnitAddCircle) :=
  Continuous.integrable_of_hasCompactSupport f.continuous (HasCompactSupport.of_compactSpace _)

lemma integral_fourier_ne_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ x : UnitAddCircle, fourier k x) = 0 := by
  have h0 : (∫ x : UnitAddCircle, fourier k x)
      = ∫ t in (0:ℝ)..(0 + 1), (fourier k : UnitAddCircle → ℂ) (t : UnitAddCircle) :=
    (UnitAddCircle.intervalIntegral_preimage 0 _).symm
  have hc : ((2 : ℂ) * Real.pi * Complex.I * k) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero, hk]
  have h1 : ∀ t : ℝ, (fourier k : UnitAddCircle → ℂ) (t : UnitAddCircle)
      = Complex.exp (((2 : ℂ) * Real.pi * Complex.I * k) * t) := by
    intro t
    rw [fourier_coe_apply]
    norm_num
  rw [h0, zero_add]
  simp only [h1]
  rw [integral_exp_mul_complex hc]
  have h2 : Complex.exp (((2 : ℂ) * Real.pi * Complex.I * k) * ((1:ℝ) : ℂ)) = 1 := by
    have h3 : ((2 : ℂ) * Real.pi * Complex.I * k) * ((1:ℝ) : ℂ)
        = (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [h3, Complex.exp_int_mul_two_pi_mul_I]
  rw [h2]
  simp

lemma integral_fourier_zero :
    (∫ x : UnitAddCircle, fourier 0 x) = 1 := by
  simp [measureReal_def]

lemma circleAvg_fourier (u : ℕ → ℝ) (k : ℤ) (N : ℕ) :
    circleAvg u (fourier k) N = weylSum u k N / N := by
  unfold circleAvg weylSum
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fourier_coe_apply]
  norm_num

lemma tendsto_circleAvg_fourier {u : ℕ → ℝ} (h : WeylVanishing u) (k : ℤ) :
    Tendsto (circleAvg u (fourier k)) atTop (𝓝 (∫ x : UnitAddCircle, fourier k x)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [integral_fourier_zero]
    have : ∀ N : ℕ, 1 ≤ N → circleAvg u (fourier 0) N = 1 := by
      intro N hN
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp [circleAvg, div_self hN']
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN using (this N hN).symm
  · rw [integral_fourier_ne_zero hk]
    exact (h k hk).congr (fun N => (circleAvg_fourier u k N).symm)

/-- The continuous functions on the circle whose Cesàro averages along `u` converge to their
integral form a submodule. -/
noncomputable def goodFuns (u : ℕ → ℝ) : Submodule ℂ C(UnitAddCircle, ℂ) where
  carrier := {f | Tendsto (circleAvg u f) atTop (𝓝 (∫ x, f x))}
  add_mem' := by
    intro f g hf hg
    have hsum : ∀ N : ℕ, circleAvg u (f + g) N = circleAvg u f N + circleAvg u g N := by
      intro N
      simp [circleAvg, Finset.sum_add_distrib, add_div]
    have hint : (∫ x, (f + g) x) = (∫ x, f x) + ∫ x, g x := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (integrable_continuousMap f) (integrable_continuousMap g)
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [hint]
    exact (hf.add hg).congr fun N => (hsum N).symm
  zero_mem' := by
    have h0 : ∀ N : ℕ, circleAvg u 0 N = 0 := fun N => by simp [circleAvg]
    have hint : (∫ x, (0 : C(UnitAddCircle, ℂ)) x) = 0 := by simp
    simp only [Set.mem_setOf_eq, hint]
    exact tendsto_const_nhds.congr fun N => (h0 N).symm
  smul_mem' := by
    intro c f hf
    have hsum : ∀ N : ℕ, circleAvg u (c • f) N = c * circleAvg u f N := by
      intro N
      simp only [circleAvg, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        mul_div_assoc]
    have hint : (∫ x, (c • f) x) = c * ∫ x, f x := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    simp only [Set.mem_setOf_eq] at hf ⊢
    rw [hint]
    exact ((tendsto_const_nhds (x := c)).mul hf).congr fun N => (hsum N).symm

lemma norm_circleAvg_sub_le (u : ℕ → ℝ) (f g : C(UnitAddCircle, ℂ)) {N : ℕ} (hN : 1 ≤ N) :
    ‖circleAvg u f N - circleAvg u g N‖ ≤ ‖f - g‖ := by
  have hrw : circleAvg u f N - circleAvg u g N
      = (∑ n ∈ Finset.range N, (f - g) (u n : UnitAddCircle)) / N := by
    simp [circleAvg, ContinuousMap.sub_apply, Finset.sum_sub_distrib, sub_div]
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  rw [hrw, norm_div]
  have h1 : ‖∑ n ∈ Finset.range N, (f - g) (u n : UnitAddCircle)‖ ≤ N * ‖f - g‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ n ∈ Finset.range N, ‖(f - g) (u n : UnitAddCircle)‖
        ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ :=
          Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm _ _
      _ = N * ‖f - g‖ := by simp
  have h2 : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [h2, div_le_iff₀ hNpos]
  calc ‖∑ n ∈ Finset.range N, (f - g) (u n : UnitAddCircle)‖ ≤ N * ‖f - g‖ := h1
    _ = ‖f - g‖ * N := by ring

lemma norm_integral_sub_le (f g : C(UnitAddCircle, ℂ)) :
    ‖(∫ x, f x) - ∫ x, g x‖ ≤ ‖f - g‖ := by
  have hsub : (∫ x, f x) - (∫ x, g x) = ∫ x, (f - g) x := by
    simp only [ContinuousMap.sub_apply]
    exact (integral_sub (integrable_continuousMap f) (integrable_continuousMap g)).symm
  rw [hsub]
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure UnitAddCircle))
    (C := ‖f - g‖) (f := fun x => (f - g) x)
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm _ _)
  simpa [measureReal_def, UnitAddCircle.measure_univ] using this

end Brockian.Equidistribution

