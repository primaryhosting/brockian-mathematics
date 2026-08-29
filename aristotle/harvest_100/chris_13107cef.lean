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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/
noncomputable def satoTateDensity (θ : ℝ) : ℝ := (2 / Real.pi) * Real.sin θ ^ 2

lemma satoTateDensity_nonneg (θ : ℝ) : 0 ≤ satoTateDensity θ := by
  have : (0:ℝ) ≤ 2 / Real.pi := by positivity
  unfold satoTateDensity
  positivity

lemma continuous_satoTateDensity : Continuous satoTateDensity := by
  unfold satoTateDensity; fun_prop

/-- The Sato–Tate measure: the probability measure on `ℝ` supported on `[0, π]`
with density `(2/π) sin²θ` with respect to Lebesgue measure. -/
noncomputable def satoTateMeasure : Measure ℝ :=
  (volume.restrict (Icc 0 Real.pi)).withDensity fun θ => ENNReal.ofReal (satoTateDensity θ)

lemma satoTate_apply {s : Set ℝ} (hs : MeasurableSet s) :
    satoTateMeasure s = ∫⁻ θ in s ∩ Icc 0 Real.pi, ENNReal.ofReal (satoTateDensity θ) := by
  rw [satoTateMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

instance : IsProbabilityMeasure satoTateMeasure := by
  constructor
  rw [satoTate_apply MeasurableSet.univ, Set.univ_inter, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le Real.pi_nonneg]
    simp [satoTateDensity, intervalIntegral.integral_const_mul, integral_sin_sq]
  · exact continuous_satoTateDensity.integrableOn_Icc
  · exact Filter.Eventually.of_forall satoTateDensity_nonneg

/-- The Sato–Tate measure as a `ProbabilityMeasure`. -/
noncomputable def satoTateProb : ProbabilityMeasure ℝ := ⟨satoTateMeasure, inferInstance⟩

@[simp] lemma satoTateProb_toMeasure : (satoTateProb : Measure ℝ) = satoTateMeasure := rfl

/-- The average of `f ∘ θ` over the primes below `X`. -/
noncomputable def primeAverage (θ : ℕ → ℝ) (f : ℝ → ℝ) (X : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesBelow X, f (θ p)) / ((Nat.primesBelow X).card : ℝ)

/-- The Sato–Tate law in its weak-convergence ("test function") form: the averages of any
bounded continuous test function over the angles `θ p`, `p` prime, converge to the integral
of the test function against the Sato–Tate measure. -/
def SatoTateWeak (θ : ℕ → ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (primeAverage θ f) atTop (𝓝 (∫ t, f t ∂satoTateMeasure))

/-- The empirical distribution of the angles `θ p` for the primes `p < X`
(with a harmless default value when there are no primes below `X`). -/
noncomputable def empirical (θ : ℕ → ℝ) (X : ℕ) : Measure ℝ :=
  if (Nat.primesBelow X).card = 0 then Measure.dirac 0
  else ((Nat.primesBelow X).card : ℝ≥0∞)⁻¹ • ∑ p ∈ Nat.primesBelow X, Measure.dirac (θ p)

lemma card_primesBelow_ne_zero {X : ℕ} (hX : 3 ≤ X) : (Nat.primesBelow X).card ≠ 0 := by
  have : 2 ∈ Nat.primesBelow X := by
    simp only [Nat.mem_primesBelow]
    exact ⟨by omega, Nat.prime_two⟩
  exact Finset.card_ne_zero_of_mem this

lemma empirical_apply (θ : ℕ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    empirical θ X s = ((Nat.primesBelow X).card : ℝ≥0∞)⁻¹ *
      (((Nat.primesBelow X).filter fun p => θ p ∈ s).card : ℝ≥0∞) := by
  rw [empirical, if_neg hX, Measure.smul_apply, Measure.coe_finset_sum]
  simp only [Finset.sum_apply, MeasureTheory.Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.sum_indicator_eq_sum_filter]
  simp

instance (θ : ℕ → ℝ) (X : ℕ) : IsProbabilityMeasure (empirical θ X) := by
  by_cases hX : (Nat.primesBelow X).card = 0
  · rw [empirical, if_pos hX]; infer_instance
  · constructor
    rw [empirical_apply θ hX MeasurableSet.univ]
    simp only [Set.mem_univ, Finset.filter_true_of_mem, implies_true]
    exact ENNReal.inv_mul_cancel (by simpa using hX) (by simp)

/-- The empirical distributions as probability measures. -/
noncomputable def empiricalProb (θ : ℕ → ℝ) (X : ℕ) : ProbabilityMeasure ℝ :=
  ⟨empirical θ X, inferInstance⟩

@[simp] lemma empiricalProb_toMeasure (θ : ℕ → ℝ) (X : ℕ) :
    (empiricalProb θ X : Measure ℝ) = empirical θ X := rfl

lemma empirical_real (θ : ℕ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (empirical θ X).real s =
      (((Nat.primesBelow X).filter fun p => θ p ∈ s).card : ℝ) /
        ((Nat.primesBelow X).card : ℝ) := by
  rw [measureReal_def, empirical_apply θ hX hs, ENNReal.toReal_mul]
  simp [div_eq_inv_mul]

lemma integral_empirical (θ : ℕ → ℝ) (f : ℝ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0) :
    ∫ t, f t ∂(empirical θ X) = primeAverage θ f X := by
  rw [empirical, if_neg hX, integral_smul_measure,
    integral_finset_sum_measure fun i _ => integrable_dirac (by simp)]
  simp only [integral_dirac, primeAverage]
  rw [ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]
  simp

lemma tendsto_empiricalProb (θ : ℕ → ℝ) (h : SatoTateWeak θ) :
    Tendsto (empiricalProb θ) atTop (𝓝 satoTateProb) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  refine (h f).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with X hX
  rw [empiricalProb_toMeasure, integral_empirical θ f (card_primesBelow_ne_zero hX)]

lemma frontier_Icc_subset (α β : ℝ) : frontier (Icc α β) ⊆ {α, β} := by
  intro x hx
  rw [frontier, closure_Icc, interior_Icc] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  simp only [Set.mem_Ioo, not_and, not_lt] at h3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases eq_or_lt_of_le h1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm h2 (h3 h))

lemma satoTate_frontier_Icc (α β : ℝ) : satoTateMeasure (frontier (Icc α β)) = 0 := by
  have habs : satoTateMeasure ≪ volume := by
    refine (withDensity_absolutelyContinuous _ _).trans ?_
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  refine habs ?_
  refine measure_mono_null (frontier_Icc_subset α β) ?_
  exact measure_union_null (measure_singleton α) (measure_singleton β)

lemma satoTate_Icc {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    satoTateMeasure.real (Icc α β) = ∫ t in α..β, satoTateDensity t := by
  have hsub : Icc α β ∩ Icc 0 Real.pi = Icc α β :=
    Set.inter_eq_self_of_subset_left (Set.Icc_subset_Icc hα hβ)
  rw [measureReal_def, satoTate_apply measurableSet_Icc, hsub,
    ← ofReal_integral_eq_lintegral_ofReal continuous_satoTateDensity.integrableOn_Icc
      (Filter.Eventually.of_forall satoTateDensity_nonneg),
    ENNReal.toReal_ofReal, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hαβ]
  exact integral_nonneg fun x => satoTateDensity_nonneg x

/-- **The Sato–Tate law for the Frobenius angles of a non-CM elliptic curve.**

Let `E/ℚ` be an elliptic curve without complex multiplication, and for a prime `p` of good
reduction write `a_p = 2√p · cos θ_p` with `θ p ∈ [0, π]` for the Frobenius angle at `p`
(the Hasse bound `|a_p| ≤ 2√p` guarantees that such an angle exists).  The Sato–Tate theorem
(Taylor, Clozel, Harris, Shepherd-Barron, …) states that the angles `θ p` are equidistributed
with respect to the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`; this is the content of the
hypothesis `SatoTateWeak θ` below, phrased as weak convergence of the empirical distributions
of the angles (i.e. convergence of averages of bounded continuous test functions).

The conclusion is the classical density statement: for `0 ≤ α ≤ β ≤ π` the proportion of primes
`p < X` whose Frobenius angle lies in `[α, β]` converges, as `X → ∞`, to `∫_α^β (2/π) sin²t dt`. -/
theorem sato_tate (θ : ℕ → ℝ) (h : SatoTateWeak θ) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto (fun X : ℕ =>
        (((Nat.primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ) /
          ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 (∫ t in α..β, (2 / Real.pi) * Real.sin t ^ 2)) := by
  have hfront : satoTateProb (frontier (Icc α β)) = 0 := by
    have := satoTate_frontier_Icc α β
    simp [ProbabilityMeasure.coeFn_def, satoTateProb_toMeasure, this]
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (tendsto_empiricalProb θ h) hfront
  have key' : Tendsto (fun X : ℕ => (empirical θ X).real (Icc α β)) atTop
      (𝓝 (satoTateMeasure.real (Icc α β))) := by
    have := (NNReal.tendsto_coe (m := fun X : ℕ => empiricalProb θ X (Icc α β))
      (f := atTop) (x := satoTateProb (Icc α β))).2 key
    simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, empiricalProb_toMeasure,
      satoTateProb_toMeasure] at this
    exact this
  rw [satoTate_Icc hα hαβ hβ] at key'
  refine key'.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with X hX
  convert empirical_real θ (card_primesBelow_ne_zero hX) (s := Icc α β) measurableSet_Icc using 3
  congr!

/-! ### Frobenius angles

For a prime `p` of good reduction of an elliptic curve `E/ℚ`, the trace of Frobenius
`a_p = p + 1 - #E(𝔽_p)` satisfies the Hasse bound `|a_p| ≤ 2√p`, so it can be written uniquely as
`a_p = 2√p · cos θ_p` with `θ_p ∈ [0, π]`; `θ_p` is the Frobenius angle at `p`. -/

/-- The Frobenius angle attached to a trace `a` at the prime `p`, i.e. the unique angle
`θ ∈ [0, π]` with `a = 2√p · cos θ` (when the Hasse bound `|a| ≤ 2√p` holds). -/
noncomputable def frobeniusAngle (a : ℤ) (p : ℕ) : ℝ := Real.arccos ((a : ℝ) / (2 * Real.sqrt p))

lemma frobeniusAngle_mem_Icc (a : ℤ) (p : ℕ) : frobeniusAngle a p ∈ Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- Under the Hasse bound, the Frobenius angle does satisfy `a = 2√p · cos θ`. -/
lemma two_sqrt_mul_cos_frobeniusAngle {a : ℤ} {p : ℕ} (hp : 0 < p)
    (h : |(a : ℝ)| ≤ 2 * Real.sqrt p) :
    2 * Real.sqrt p * Real.cos (frobeniusAngle a p) = (a : ℝ) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  have h2 : 0 < 2 * Real.sqrt p := by linarith
  have habs : |(a : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos h2, div_le_one h2]
    exact h
  rw [frobeniusAngle, Real.cos_arccos (by cases abs_le.mp habs; linarith) (abs_le.mp habs).2]
  field_simp

/-- **Sato–Tate for a sequence of Frobenius traces.**  If `a p` is the trace of Frobenius at `p`
of a non-CM elliptic curve over `ℚ` (satisfying the Hasse bound `|a p| ≤ 2√p`), and if the
associated Frobenius angles `θ p = arccos (a p / (2√p))` obey the Sato–Tate law in its weak form,
then for `0 ≤ α ≤ β ≤ π` the proportion of primes `p < X` with `θ p ∈ [α, β]` converges to
`∫_α^β (2/π) sin²t dt`. -/
theorem sato_tate_of_traces (a : ℕ → ℤ)
    (h : SatoTateWeak fun p => frobeniusAngle (a p) p) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto (fun X : ℕ =>
        (((Nat.primesBelow X).filter fun p => frobeniusAngle (a p) p ∈ Icc α β).card : ℝ) /
          ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 (∫ t in α..β, (2 / Real.pi) * Real.sin t ^ 2)) :=
  sato_tate _ h hα hαβ hβ


/-! ### The counting form of the Sato–Tate law, and its equivalence with the weak form -/

/-- The proportion of primes `p < X` whose angle `θ p` lies in the set `s`. -/
noncomputable def primeRatio (θ : ℕ → ℝ) (s : Set ℝ) (X : ℕ) : ℝ :=
  (((Nat.primesBelow X).filter fun p => θ p ∈ s).card : ℝ) / ((Nat.primesBelow X).card : ℝ)

/-- The Sato–Tate law in its classical "counting" form: for `0 ≤ α ≤ β ≤ π`, the proportion of
primes `p < X` with `θ p ∈ [α, β]` tends to `∫_α^β (2/π) sin²t dt`. -/
def SatoTateCounting (θ : ℕ → ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ Real.pi →
    Tendsto (primeRatio θ (Icc α β)) atTop (𝓝 (∫ t in α..β, satoTateDensity t))

lemma empirical_real_eq_primeRatio (θ : ℕ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) : (empirical θ X).real s = primeRatio θ s X :=
  empirical_real θ hX hs

lemma satoTate_singleton (c : ℝ) : satoTateMeasure {c} = 0 := by
  have habs : satoTateMeasure ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  exact habs (measure_singleton c)

lemma satoTate_inter_Icc {s : Set ℝ} (hs : MeasurableSet s) :
    satoTateMeasure s = satoTateMeasure (s ∩ Icc 0 Real.pi) := by
  rw [satoTate_apply hs, satoTate_apply (hs.inter measurableSet_Icc), Set.inter_assoc,
    Set.inter_self]

lemma empirical_real_inter_Icc (θ : ℕ → ℝ) (hmem : ∀ p, θ p ∈ Icc 0 Real.pi) (X : ℕ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (empirical θ X).real s = (empirical θ X).real (s ∩ Icc 0 Real.pi) := by
  by_cases hX : (Nat.primesBelow X).card = 0
  · rw [empirical, if_pos hX]
    simp only [measureReal_def, Measure.dirac_apply' _ hs,
      Measure.dirac_apply' _ (hs.inter measurableSet_Icc)]
    have h0 : (0:ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, Real.pi_nonneg⟩
    by_cases h0s : (0:ℝ) ∈ s
    · simp [h0s, h0]
    · simp [h0s]

  · have hfil : ((Nat.primesBelow X).filter fun p => θ p ∈ s)
        = ((Nat.primesBelow X).filter fun p => θ p ∈ s ∩ Icc 0 Real.pi) :=
      Finset.filter_congr fun p _ => by simp only [Set.mem_inter_iff, and_iff_left (hmem p)]
    rw [empirical_real θ hX hs, empirical_real θ hX (hs.inter measurableSet_Icc), hfil]
    congr!

/-- Any open interval, intersected with `[0, π]`, is squeezed between a closed subinterval
`[α, β]` of `[0, π]` and that subinterval together with its two endpoints. -/
lemma exists_Icc_squeeze (a b : ℝ) : ∃ α β : ℝ, 0 ≤ α ∧ α ≤ β ∧ β ≤ Real.pi ∧
    Ioo a b ∩ Icc 0 Real.pi ⊆ Icc α β ∧ Icc α β ⊆ (Ioo a b ∩ Icc 0 Real.pi) ∪ {α, β} := by
  have hpi : (0:ℝ) ≤ Real.pi := Real.pi_nonneg
  refine ⟨min (max a 0) Real.pi, max (min b Real.pi) (min (max a 0) Real.pi), ?_, ?_, ?_, ?_, ?_⟩
  · exact le_min (le_max_right _ _) hpi
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (min_le_right _ _)
  · rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨min_le_of_left_le (max_le h1.le h3), le_max_of_le_left (le_min h2.le h4)⟩
  · rintro x ⟨h1, h2⟩
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    have hx0 : 0 ≤ x := le_trans (le_min (le_max_right _ _) hpi) h1
    have hxpi : x ≤ Real.pi := le_trans h2 (max_le (min_le_right _ _) (min_le_right _ _))
    by_cases hax : a < x
    · by_cases hxb : x < b
      · exact Or.inl ⟨⟨hax, hxb⟩, ⟨hx0, hxpi⟩⟩
      · push_neg at hxb
        rw [min_eq_left (le_trans hxb hxpi)] at h2 ⊢
        exact Or.inr (Or.inr (le_antisymm h2 (max_le hxb h1)))
    · push_neg at hax
      refine Or.inr (Or.inl (le_antisymm ?_ h1))
      rcases le_total a 0 with ha | ha
      · rw [max_eq_right ha]; exact le_min (hax.trans ha) hxpi
      · rw [max_eq_left ha]; exact le_min hax hxpi

/-- Under the counting form of the Sato–Tate law, the proportion of primes whose angle equals a
given value tends to zero. -/
lemma tendsto_primeRatio_singleton (θ : ℕ → ℝ) (h : SatoTateCounting θ) {c : ℝ}
    (hc0 : 0 ≤ c) (hcpi : c ≤ Real.pi) :
    Tendsto (fun X => (empirical θ X).real {c}) atTop (𝓝 0) := by
  have hlim := h c c hc0 le_rfl hcpi
  simp only [intervalIntegral.integral_same] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with X hX
  rw [Set.Icc_self, empirical_real θ (card_primesBelow_ne_zero hX) (measurableSet_singleton c),
    primeRatio]

/-- Under the counting form of the Sato–Tate law, the empirical measures of the angles converge
weakly to the Sato–Tate measure. -/
lemma tendsto_empiricalProb_of_counting (θ : ℕ → ℝ) (hmem : ∀ p, θ p ∈ Icc 0 Real.pi)
    (h : SatoTateCounting θ) : Tendsto (empiricalProb θ) atTop (𝓝 satoTateProb) := by
  have key : ∀ a b : ℝ, Tendsto (fun X => (empirical θ X).real (Ioo a b)) atTop
      (𝓝 (satoTateMeasure.real (Ioo a b))) := by
    intro a b
    obtain ⟨α, β, hα, hαβ, hβ, hsub, hsup⟩ := exists_Icc_squeeze a b
    have hIcc : Tendsto (fun X => (empirical θ X).real (Icc α β)) atTop
        (𝓝 (satoTateMeasure.real (Icc α β))) := by
      rw [satoTate_Icc hα hαβ hβ]
      refine (h α β hα hαβ hβ).congr' ?_
      filter_upwards [eventually_ge_atTop 3] with X hX
      rw [empirical_real θ (card_primesBelow_ne_zero hX) measurableSet_Icc]
      rfl
    have hatoms : Tendsto (fun X => (empirical θ X).real {α} + (empirical θ X).real {β})
        atTop (𝓝 0) := by
      have := (tendsto_primeRatio_singleton θ h hα (hαβ.trans hβ)).add
        (tendsto_primeRatio_singleton θ h (hα.trans hαβ) hβ)
      simpa using this
    -- the empirical measure of `Ioo a b` differs from that of `Icc α β` by at most the atoms
    have hd : ∀ X, |(empirical θ X).real (Ioo a b) - (empirical θ X).real (Icc α β)| ≤
        (empirical θ X).real {α} + (empirical θ X).real {β} := by
      intro X
      have h1 : (empirical θ X).real (Ioo a b) = (empirical θ X).real (Ioo a b ∩ Icc 0 Real.pi) :=
        empirical_real_inter_Icc θ hmem X measurableSet_Ioo
      have hle1 : (empirical θ X).real (Ioo a b) ≤ (empirical θ X).real (Icc α β) := by
        rw [h1]; exact measureReal_mono hsub
      have hle2 : (empirical θ X).real (Icc α β) ≤ (empirical θ X).real (Ioo a b)
          + ((empirical θ X).real {α} + (empirical θ X).real {β}) := by
        calc (empirical θ X).real (Icc α β)
            ≤ (empirical θ X).real ((Ioo a b ∩ Icc 0 Real.pi) ∪ {α, β}) := measureReal_mono hsup
          _ ≤ (empirical θ X).real (Ioo a b ∩ Icc 0 Real.pi)
              + (empirical θ X).real ({α, β} : Set ℝ) := measureReal_union_le _ _
          _ ≤ (empirical θ X).real (Ioo a b)
              + ((empirical θ X).real {α} + (empirical θ X).real {β}) := by
              rw [h1]
              have : (({α, β} : Set ℝ)) = {α} ∪ {β} := rfl
              gcongr
              rw [this]
              exact measureReal_union_le _ _
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hST : satoTateMeasure.real (Ioo a b) = satoTateMeasure.real (Icc α β) := by
      have h1 : satoTateMeasure (Ioo a b) = satoTateMeasure (Ioo a b ∩ Icc 0 Real.pi) :=
        satoTate_inter_Icc measurableSet_Ioo
      have hle1 : satoTateMeasure (Ioo a b) ≤ satoTateMeasure (Icc α β) := by
        rw [h1]; exact measure_mono hsub
      have hle2 : satoTateMeasure (Icc α β) ≤ satoTateMeasure (Ioo a b) := by
        calc satoTateMeasure (Icc α β)
            ≤ satoTateMeasure ((Ioo a b ∩ Icc 0 Real.pi) ∪ {α, β}) := measure_mono hsup
          _ ≤ satoTateMeasure (Ioo a b ∩ Icc 0 Real.pi) + satoTateMeasure ({α, β} : Set ℝ) :=
              measure_union_le _ _
          _ = satoTateMeasure (Ioo a b) := by
              rw [← h1]
              have : satoTateMeasure ({α, β} : Set ℝ) = 0 :=
                measure_union_null (satoTate_singleton α) (satoTate_singleton β)
              rw [this, add_zero]
      rw [measureReal_def, measureReal_def, le_antisymm hle1 hle2]
    rw [hST]
    have hzero : Tendsto
        (fun X => (empirical θ X).real (Ioo a b) - (empirical θ X).real (Icc α β)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun X => by simpa only [Real.norm_eq_abs] using hd X) hatoms
    simpa using hzero.add hIcc
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (S := {s : Set ℝ | ∃ a b : ℝ, s = Ioo a b}) ?_ ?_ ?_ ?_
  · rintro s ⟨a, b, rfl⟩ t ⟨c, d, rfl⟩ -
    exact ⟨max a c, min b d, by rw [Set.Ioo_inter_Ioo]⟩
  · rintro s ⟨a, b, rfl⟩
    exact measurableSet_Ioo
  · intro u hu x hx
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
    exact ⟨Ioo a b, ⟨a, b, rfl⟩, Ioo_mem_nhds hab.1 hab.2, hsub⟩
  · rintro s ⟨a, b, rfl⟩
    have hkey := key a b
    rw [← NNReal.tendsto_coe]
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, empiricalProb_toMeasure,
      satoTateProb_toMeasure] using hkey

/-- The two forms of the Sato–Tate law agree, for a sequence of angles taking values in `[0, π]`:
weak convergence of the empirical distributions is equivalent to the classical statement about
the densities of primes whose angle lies in a given subinterval of `[0, π]`. -/
theorem satoTateWeak_iff_satoTateCounting (θ : ℕ → ℝ) (hmem : ∀ p, θ p ∈ Icc 0 Real.pi) :
    SatoTateWeak θ ↔ SatoTateCounting θ := by
  constructor
  · intro h α β hα hαβ hβ
    have hlim := sato_tate θ h hα hαβ hβ
    simp only [satoTateDensity]
    exact hlim.congr' (Eventually.of_forall fun X => by simp only [primeRatio]; congr!)
  · intro h f
    have hconv := tendsto_empiricalProb_of_counting θ hmem h
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
    have := hconv f
    simp only [empiricalProb_toMeasure, satoTateProb_toMeasure] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with X hX
    exact integral_empirical θ f (card_primesBelow_ne_zero hX)


/-! ### Moments of the Sato–Tate distribution

Writing `a_p = 2√p cos θ_p`, the first two moments of the Sato–Tate distribution say that
`a_p / √p` has average `0` and `a_p² / p` has average `1`. -/

lemma satoTate_integral (f : ℝ → ℝ) :
    ∫ t, f t ∂satoTateMeasure = ∫ t in (0:ℝ)..Real.pi, satoTateDensity t * f t := by
  have hd : (fun θ => ENNReal.ofReal (satoTateDensity θ))
      = fun θ => ((Real.toNNReal (satoTateDensity θ) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [satoTateMeasure, hd,
    integral_withDensity_eq_integral_smul (by unfold satoTateDensity; fun_prop),
    intervalIntegral.integral_of_le Real.pi_nonneg, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  simp [NNReal.smul_def, Real.coe_toNNReal _ (satoTateDensity_nonneg x)]

/-- The first moment of the Sato–Tate distribution vanishes: `∫ 2cos θ dμ_ST = 0`. -/
theorem satoTate_first_moment : ∫ t, 2 * Real.cos t ∂satoTateMeasure = 0 := by
  rw [satoTate_integral]
  have h : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (4 / Real.pi) * Real.sin t ^ 3 / 3)
      (satoTateDensity t * (2 * Real.cos t)) t := by
    intro t
    have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 3) (3 * Real.sin t ^ 2 * Real.cos t) t := by
      simpa using ((Real.hasDerivAt_sin t).pow 3)
    have h2 := (hs.const_mul (4 / Real.pi)).div_const 3
    convert h2 using 1
    unfold satoTateDensity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t)
    (by unfold satoTateDensity; apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- The second moment of the Sato–Tate distribution is `1`: `∫ (2cos θ)² dμ_ST = 1`. -/
theorem satoTate_second_moment : ∫ t, (2 * Real.cos t) ^ 2 ∂satoTateMeasure = 1 := by
  rw [satoTate_integral]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t / Real.pi - Real.sin (4 * t) / (4 * Real.pi))
      (satoTateDensity t * (2 * Real.cos t) ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t / Real.pi) (1 / Real.pi) t := by
      simpa using (hasDerivAt_id t).div_const Real.pi
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (4 * t) / (4 * Real.pi))
        (4 * Real.cos (4 * t) / (4 * Real.pi)) t := by
      have := ((Real.hasDerivAt_sin (4 * t)).comp t ((hasDerivAt_id t).const_mul 4)).div_const
        (4 * Real.pi)
      simpa [mul_comm] using this
    have h3 := h1.sub h2
    have hc : Real.cos (4 * t) = 1 - 8 * (Real.sin t ^ 2 * Real.cos t ^ 2) := by
      have h4 : (4 : ℝ) * t = 2 * (2 * t) := by ring
      rw [h4, Real.cos_two_mul, Real.cos_two_mul, Real.sin_sq]
      ring
    convert h3 using 1
    rw [hc]
    unfold satoTateDensity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t)
    (by unfold satoTateDensity; apply Continuous.intervalIntegrable; fun_prop)]
  have hs : Real.sin (4 * Real.pi) = 0 := by
    have h4 : (4:ℝ) * Real.pi = 2 * (2 * Real.pi) := by ring
    rw [h4]
    simp [Real.sin_two_mul]
  rw [hs]
  field_simp
  norm_num

/-- The bounded continuous function `θ ↦ 2 cos θ`. -/
noncomputable def twoCosBCF : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => 2 * Real.cos t) (by fun_prop) 2
    (fun t => by
      simp only [Real.norm_eq_abs, abs_mul]
      have := Real.abs_cos_le_one t
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      nlinarith)

/-- The bounded continuous function `θ ↦ (2 cos θ)²`. -/
noncomputable def twoCosSqBCF : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (2 * Real.cos t) ^ 2) (by fun_prop) 4
    (fun t => by
      simp only [Real.norm_eq_abs, abs_pow, abs_mul]
      have := Real.abs_cos_le_one t
      have h0 : |(2:ℝ)| = 2 := by norm_num
      rw [h0]
      nlinarith [abs_nonneg (Real.cos t)])

/-- Under the Sato–Tate law, the averages of `a_p/√p = 2 cos θ_p` over the primes tend to `0`. -/
theorem tendsto_primeAverage_two_cos (θ : ℕ → ℝ) (h : SatoTateWeak θ) :
    Tendsto (primeAverage θ fun t => 2 * Real.cos t) atTop (𝓝 0) := by
  have := h twoCosBCF
  rwa [show (∫ t, twoCosBCF t ∂satoTateMeasure) = 0 from satoTate_first_moment] at this

/-- Under the Sato–Tate law, the averages of `a_p²/p = (2 cos θ_p)²` over the primes tend to `1`. -/
theorem tendsto_primeAverage_two_cos_sq (θ : ℕ → ℝ) (h : SatoTateWeak θ) :
    Tendsto (primeAverage θ fun t => (2 * Real.cos t) ^ 2) atTop (𝓝 1) := by
  have := h twoCosSqBCF
  rwa [show (∫ t, twoCosSqBCF t ∂satoTateMeasure) = 1 from satoTate_second_moment] at this


end Math2

