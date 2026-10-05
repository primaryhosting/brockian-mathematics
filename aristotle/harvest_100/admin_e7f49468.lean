/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Filter Set
open scoped Topology ENNReal Nat

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The density of the Sato–Tate measure with respect to Lebesgue measure on `[0, π]`:
`θ ↦ (2/π) sin²θ`. -/
noncomputable def satoTateDensity (θ : ℝ) : ℝ := 2 / π * Real.sin θ ^ 2

/-- The Sato–Tate measure on `ℝ`: the measure supported on `[0, π]` with density
`(2/π) sin²θ` with respect to Lebesgue measure. -/
noncomputable def satoTateMeasure : Measure ℝ :=
  (volume.restrict (Set.Icc 0 π)).withDensity fun θ => ENNReal.ofReal (satoTateDensity θ)

/-- The Frobenius angle `θ_p ∈ [0, π]` attached to a trace of Frobenius `a p`, defined by
`a p = 2 √p cos θ_p`. -/
noncomputable def frobeniusAngle (a : ℕ → ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((a p : ℝ) / (2 * Real.sqrt p))

open scoped Classical in
/-- The Sato–Tate equidistribution statement for a sequence `a` of traces of Frobenius:
the Frobenius angles `θ_p` become equidistributed in `[0, π]` with respect to the
Sato–Tate measure, as `p` ranges over the primes.  This is the conclusion of the
Sato–Tate theorem for an elliptic curve over `ℚ` without complex multiplication. -/
def SatoTateEquidistributed (a : ℕ → ℤ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ π →
    Tendsto
      (fun X : ℕ =>
        (((Nat.primesBelow X).filter fun p => frobeniusAngle a p ∈ Set.Icc s t).card : ℝ) /
          ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 (satoTateMeasure (Set.Icc s t)).toReal)

/-! ## Basic properties of the density -/

lemma satoTateDensity_nonneg (θ : ℝ) : 0 ≤ satoTateDensity θ := by
  have hpi : (0:ℝ) < π := pi_pos
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma continuous_satoTateDensity : Continuous satoTateDensity := by
  unfold satoTateDensity; fun_prop

/-- The Sato–Tate measure of a measurable set is the integral of the density over the part
of the set lying inside `[0, π]`. -/
lemma satoTateMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    satoTateMeasure s = ENNReal.ofReal (∫ θ in s ∩ Set.Icc 0 π, satoTateDensity θ) := by
  rw [satoTateMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs,
    ← ofReal_integral_eq_lintegral_ofReal]
  · exact continuous_satoTateDensity.integrableOn_Icc.mono_set Set.inter_subset_right
  · exact Filter.Eventually.of_forall satoTateDensity_nonneg

/-- The distribution function of the Sato–Tate density. -/
lemma integral_satoTateDensity (s t : ℝ) :
    ∫ θ in s..t, satoTateDensity θ
      = (Real.sin s * Real.cos s - Real.sin t * Real.cos t + t - s) / π := by
  have hpi : (0:ℝ) < π := pi_pos
  simp only [satoTateDensity, intervalIntegral.integral_const_mul, integral_sin_sq]
  field_simp

/-- The Sato–Tate measure of an interval `[s, t] ⊆ [0, π]`. -/
lemma satoTateMeasure_Icc {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ π) :
    satoTateMeasure (Set.Icc s t) = ENNReal.ofReal (∫ θ in s..t, satoTateDensity θ) := by
  rw [satoTateMeasure_apply measurableSet_Icc,
    Set.inter_eq_self_of_subset_left (Set.Icc_subset_Icc h0 ht),
    intervalIntegral.integral_of_le hst, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The Sato–Tate measure is a probability measure. -/
instance : IsProbabilityMeasure satoTateMeasure := by
  constructor
  have hpi : (0:ℝ) < π := pi_pos
  rw [satoTateMeasure_apply MeasurableSet.univ, Set.univ_inter,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le pi_pos.le,
    integral_satoTateDensity]
  simp [hpi.ne']

/-- Integration against the Sato–Tate measure is integration of `density · g` over `[0, π]`. -/
lemma integral_satoTateMeasure (g : ℝ → ℝ) :
    ∫ θ, g θ ∂satoTateMeasure = ∫ θ in (0:ℝ)..π, satoTateDensity θ * g θ := by
  rw [satoTateMeasure, integral_withDensity_eq_integral_toReal_smul
    continuous_satoTateDensity.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g,
    intervalIntegral.integral_of_le pi_pos.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp [ENNReal.toReal_ofReal (satoTateDensity_nonneg θ), smul_eq_mul]

/-- The measure of `[s, t] ⊆ [0, π]`, as a real number. -/
lemma satoTateMeasure_Icc_toReal {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ π) :
    (satoTateMeasure (Set.Icc s t)).toReal = ∫ θ in s..t, 2 / π * Real.sin θ ^ 2 := by
  rw [satoTateMeasure_Icc h0 hst ht, ENNReal.toReal_ofReal]
  · rfl
  · exact intervalIntegral.integral_nonneg hst fun θ _ => satoTateDensity_nonneg θ

/-! ## Moments of the Sato–Tate distribution -/

/-- The Wallis-type integral `∫₀^π cosⁿ`. -/
noncomputable def wallisCos (n : ℕ) : ℝ := ∫ x in (0:ℝ)..π, Real.cos x ^ n

lemma wallisCos_zero : wallisCos 0 = π := by simp [wallisCos]

lemma wallisCos_rec (n : ℕ) : wallisCos (n + 2) = (n + 1) / (n + 2) * wallisCos n := by
  simp [wallisCos, integral_cos_pow]

lemma wallisCos_odd (n : ℕ) : wallisCos (2 * n + 1) = 0 := by
  induction n with
  | zero => simp [wallisCos]
  | succ k ih =>
      have h : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
      rw [h, wallisCos_rec, ih, mul_zero]

lemma wallisCos_even (n : ℕ) : wallisCos (2 * n) = π * (n.centralBinom : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp [wallisCos, Nat.centralBinom]
  | succ k ih =>
      have h : 2 * (k + 1) = 2 * k + 2 := by ring
      have hc : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
          = 2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ k)
      rw [h, wallisCos_rec, ih]
      push_cast
      field_simp
      linear_combination (-2 * 4 ^ k : ℝ) * hc

/-- The moments of the trace `2 cos θ` against the Sato–Tate measure, in terms of Wallis
integrals. -/
lemma satoTate_moment (k : ℕ) :
    ∫ θ, (2 * Real.cos θ) ^ k ∂satoTateMeasure =
      2 / π * 2 ^ k * (wallisCos k - wallisCos (k + 2)) := by
  rw [integral_satoTateMeasure]
  have key : (∫ θ in (0:ℝ)..π, satoTateDensity θ * (2 * Real.cos θ) ^ k)
      = ∫ θ in (0:ℝ)..π, ((2 / π * 2 ^ k) * Real.cos θ ^ k
          - (2 / π * 2 ^ k) * Real.cos θ ^ (k + 2)) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [satoTateDensity, mul_pow, Real.sin_sq]
    ring
  rw [key, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, wallisCos, wallisCos]
  ring

/-- The even moments of the Sato–Tate distribution are the Catalan numbers. -/
lemma satoTate_moment_even (n : ℕ) :
    ∫ θ, (2 * Real.cos θ) ^ (2 * n) ∂satoTateMeasure = (catalan n : ℝ) := by
  have hpi : (0:ℝ) < π := pi_pos
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (succ_mul_catalan_eq_centralBinom n)
  have h2 : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
      = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ n)
  have h3 : 2 * n + 2 = 2 * (n + 1) := by ring
  have h4 : (2:ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  rw [satoTate_moment, wallisCos_even, h3, wallisCos_even, h4]
  have expand : 2 / π * 4 ^ n * (π * (Nat.centralBinom n : ℝ) / 4 ^ n
      - π * (Nat.centralBinom (n + 1) : ℝ) / 4 ^ (n + 1))
      = 2 * (Nat.centralBinom n : ℝ) - (Nat.centralBinom (n + 1) : ℝ) / 2 := by
    have h4' : (4:ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  rw [expand]
  refine mul_left_cancel₀ hn ?_
  linear_combination -h1 - (1/2 : ℝ) * h2

/-- The odd moments of the Sato–Tate distribution vanish. -/
lemma satoTate_moment_odd (n : ℕ) :
    ∫ θ, (2 * Real.cos θ) ^ (2 * n + 1) ∂satoTateMeasure = 0 := by
  have h : 2 * n + 1 + 2 = 2 * (n + 1) + 1 := by ring
  rw [satoTate_moment, wallisCos_odd, h, wallisCos_odd]
  ring

/-! ## Frobenius angles -/

lemma frobeniusAngle_mem_Icc (a : ℕ → ℤ) (p : ℕ) : frobeniusAngle a p ∈ Set.Icc 0 π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- Under the Hasse bound `|a p| ≤ 2 √p`, the Frobenius angle satisfies `a p = 2 √p cos θ_p`. -/
lemma cos_frobeniusAngle {a : ℕ → ℤ} {p : ℕ} (hp : p.Prime)
    (hasse : |(a p : ℝ)| ≤ 2 * Real.sqrt p) :
    (a p : ℝ) = 2 * Real.sqrt p * Real.cos (frobeniusAngle a p) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hden : (0:ℝ) < 2 * Real.sqrt p := by linarith
  have habs : |(a p : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos hden, div_le_one hden]
    exact hasse
  have h1 := abs_le.mp habs
  rw [frobeniusAngle, Real.cos_arccos h1.1 h1.2]
  field_simp

/-! ## The Sato–Tate statement -/

open scoped Classical in
/-- **The Sato–Tate distribution of Frobenius angles.**

For an elliptic curve `E / ℚ` without complex multiplication, the Frobenius angles
`θ_p ∈ [0, π]`, defined by `a_p = 2 √p cos θ_p` (well defined by the Hasse bound), are
equidistributed with respect to the *Sato–Tate measure* `μ_ST = (2/π) sin²θ dθ` on `[0, π]`.

This theorem records the precise content of that statement:

1. `μ_ST` is a probability measure on `[0, π]`;
2. its distribution function is explicit:
   `μ_ST [s,t] = (1/π)(t - s + sin s cos s - sin t cos t)`;
3. its even moments in the trace variable `2 cos θ` are the Catalan numbers, and
4. its odd moments vanish (these moments characterise `μ_ST` among measures on `[0, π]`);
5. the Frobenius angles are well-defined elements of `[0, π]` recovering `a_p = 2 √p cos θ_p`;
6. the equidistribution statement `SatoTateEquidistributed` is exactly the assertion that the
   proportion of primes `p < X` with `θ_p ∈ [s, t]` tends to `∫ₛᵗ (2/π) sin²θ dθ`. -/
theorem sato_tate :
    IsProbabilityMeasure satoTateMeasure ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ π →
      satoTateMeasure (Set.Icc s t) =
        ENNReal.ofReal ((t - s + Real.sin s * Real.cos s - Real.sin t * Real.cos t) / π)) ∧
    (∀ n : ℕ, ∫ θ, (2 * Real.cos θ) ^ (2 * n) ∂satoTateMeasure = (catalan n : ℝ)) ∧
    (∀ n : ℕ, ∫ θ, (2 * Real.cos θ) ^ (2 * n + 1) ∂satoTateMeasure = 0) ∧
    (∀ (a : ℕ → ℤ) (p : ℕ), p.Prime → |(a p : ℝ)| ≤ 2 * Real.sqrt p →
      frobeniusAngle a p ∈ Set.Icc 0 π ∧
        (a p : ℝ) = 2 * Real.sqrt p * Real.cos (frobeniusAngle a p)) ∧
    (∀ a : ℕ → ℤ, SatoTateEquidistributed a ↔
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ π →
        Tendsto
          (fun X : ℕ =>
            (((Nat.primesBelow X).filter fun p =>
                frobeniusAngle a p ∈ Set.Icc s t).card : ℝ) /
              ((Nat.primesBelow X).card : ℝ))
          atTop (𝓝 (∫ θ in s..t, 2 / π * Real.sin θ ^ 2))) := by
  refine ⟨inferInstance, ?_, satoTate_moment_even, satoTate_moment_odd,
    fun a p hp hasse => ⟨frobeniusAngle_mem_Icc a p, cos_frobeniusAngle hp hasse⟩, ?_⟩
  · intro s t h0 hst ht
    rw [satoTateMeasure_Icc h0 hst ht, integral_satoTateDensity]
    ring_nf
  · intro a
    constructor
    · intro h s t h0 hst ht
      have := h s t h0 hst ht
      rwa [satoTateMeasure_Icc_toReal h0 hst ht] at this
    · intro h s t h0 hst ht
      have := h s t h0 hst ht
      rwa [satoTateMeasure_Icc_toReal h0 hst ht]

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

