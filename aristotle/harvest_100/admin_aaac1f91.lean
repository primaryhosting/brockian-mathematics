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
open scoped ENNReal NNReal BoundedContinuousFunction

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

namespace Math2

open MeasureTheory Filter Topology Set

/-! ## The Sato–Tate measure -/

/-- The Sato–Tate measure on `ℝ`: the probability measure supported on `[0, π]` with
density `(2/π) · sin²θ` with respect to Lebesgue measure. -/
noncomputable def satoTateMeasure : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Real.pi)).withDensity
    (fun θ => ENNReal.ofReal (2 / Real.pi * Real.sin θ ^ 2))

theorem satoTate_apply (s : Set ℝ) (hs : MeasurableSet s) :
    satoTateMeasure s = ENNReal.ofReal (∫ θ in s ∩ Set.Icc 0 Real.pi,
      2 / Real.pi * Real.sin θ ^ 2) := by
  have hcont : Continuous (fun θ : ℝ => 2 / Real.pi * Real.sin θ ^ 2) := by fun_prop
  rw [satoTateMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · exact (hcont.integrableOn_Icc (a := 0) (b := Real.pi)).mono_set inter_subset_right
  · filter_upwards with x
    positivity

/-- The integral of the Sato–Tate density over a subinterval, in closed form. -/
theorem integral_satoTate_density {α β : ℝ} (h : α ≤ β) :
    (∫ θ in Set.Icc α β, 2 / Real.pi * Real.sin θ ^ 2)
      = (Real.sin α * Real.cos α - Real.sin β * Real.cos β + β - α) / Real.pi := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
    intervalIntegral.integral_const_mul, integral_sin_sq]
  have := Real.pi_pos
  field_simp

theorem satoTate_univ : satoTateMeasure Set.univ = 1 := by
  rw [satoTate_apply _ MeasurableSet.univ, Set.univ_inter,
    integral_satoTate_density Real.pi_pos.le]
  have := Real.pi_pos
  simp [Real.sin_pi, Real.sin_zero]

instance : IsProbabilityMeasure satoTateMeasure := ⟨satoTate_univ⟩

/-- The Sato–Tate measure as a bundled probability measure. -/
noncomputable def satoTateProb : ProbabilityMeasure ℝ := ⟨satoTateMeasure, inferInstance⟩

/-- The Sato–Tate mass of an interval `[α, β] ⊆ [0, π]`, in closed form. -/
noncomputable def satoTateMass (α β : ℝ) : ℝ :=
  (Real.sin α * Real.cos α - Real.sin β * Real.cos β + β - α) / Real.pi

theorem satoTateMass_nonneg {α β : ℝ} (hαβ : α ≤ β) : 0 ≤ satoTateMass α β := by
  rw [satoTateMass, ← integral_satoTate_density hαβ]
  refine setIntegral_nonneg measurableSet_Icc (fun x _ => ?_)
  have := Real.pi_pos
  positivity

theorem satoTate_Icc {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    satoTateMeasure (Set.Icc α β) = ENNReal.ofReal (satoTateMass α β) := by
  rw [satoTate_apply _ measurableSet_Icc,
    Set.inter_eq_self_of_subset_left (Set.Icc_subset_Icc hα hβ),
    integral_satoTate_density hαβ, satoTateMass]

theorem satoTate_absolutelyContinuous : satoTateMeasure ≪ (volume : Measure ℝ) :=
  (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem satoTate_frontier_Icc (α β : ℝ) :
    satoTateMeasure (frontier (Set.Icc α β)) = 0 := by
  refine satoTate_absolutelyContinuous ?_
  refine measure_mono_null (t := ({α, β} : Set ℝ)) ?_
    (((Set.finite_singleton β).insert α).measure_zero volume)
  rw [frontier, closure_Icc, interior_Icc]
  intro x hx
  simp only [Set.mem_diff, Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hx with ⟨⟨h1, h2⟩, h3 | h3⟩
  · exact Or.inl (le_antisymm h3 h1)
  · exact Or.inr (le_antisymm h2 h3)

theorem satoTate_integral (f : ℝ →ᵇ ℝ) :
    ∫ θ, f θ ∂satoTateMeasure = ∫ θ in (0:ℝ)..Real.pi, 2 / Real.pi * Real.sin θ ^ 2 * f θ := by
  have hpi := Real.pi_pos
  rw [satoTateMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  rw [intervalIntegral.integral_of_le hpi.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [smul_eq_mul]

/-! ## Frobenius angles and empirical distributions -/

/-- The Frobenius angle `θ_p ∈ [0, π]` attached to the trace of Frobenius `a_p` of an
elliptic curve at a prime `p` of good reduction: it is defined by `a_p = 2√p · cos θ_p`,
which makes sense because of the Hasse bound `|a_p| ≤ 2√p`. -/
noncomputable def frobAngle (a : ℕ → ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((a p : ℝ) / (2 * Real.sqrt p))

/-- The empirical (uniform) probability distribution of the angles `θ p` for `p` prime, `p < X`.
(If there are no primes below `X`, an arbitrary probability measure is used.) -/
noncomputable def angleEmpirical (θ : ℕ → ℝ) (X : ℕ) : Measure ℝ :=
  if (Nat.primesBelow X).card = 0 then Measure.dirac 0
  else ((Nat.primesBelow X).card : ℝ≥0∞)⁻¹ • ∑ p ∈ Nat.primesBelow X, Measure.dirac (θ p)

theorem angleEmpirical_apply (θ : ℕ → ℝ) (X : ℕ) (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    angleEmpirical θ X s =
      ((Nat.primesBelow X).filter (fun p => θ p ∈ s)).card / ((Nat.primesBelow X).card : ℝ≥0∞) := by
  rw [angleEmpirical, if_neg hX, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [MeasureTheory.Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp [smul_eq_mul, ENNReal.div_eq_inv_mul]

instance (θ : ℕ → ℝ) (X : ℕ) : IsProbabilityMeasure (angleEmpirical θ X) := by
  constructor
  by_cases hX : (Nat.primesBelow X).card = 0
  · rw [angleEmpirical, if_pos hX]
    simp
  · rw [angleEmpirical_apply θ X hX MeasurableSet.univ]
    simp only [Set.mem_univ, Finset.filter_true]
    exact ENNReal.div_self (by exact_mod_cast hX) (ENNReal.natCast_ne_top _)

/-- The empirical distribution as a bundled probability measure. -/
noncomputable def angleEmpiricalProb (θ : ℕ → ℝ) (X : ℕ) : ProbabilityMeasure ℝ :=
  ⟨angleEmpirical θ X, inferInstance⟩

theorem angleEmpirical_integral (θ : ℕ → ℝ) (X : ℕ) (hX : (Nat.primesBelow X).card ≠ 0)
    (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(angleEmpirical θ X) =
      (∑ p ∈ Nat.primesBelow X, f (θ p)) / ((Nat.primesBelow X).card : ℝ) := by
  rw [angleEmpirical, if_neg hX, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_finset_sum_measure (fun i _ => (f.integrable _))]
  simp only [MeasureTheory.integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_inv_mul]

/-! ## The Sato–Tate law -/

/-- The Sato–Tate law for a sequence of angles `θ : ℕ → ℝ`: the angles `θ p`, for `p` running
over the primes, are equidistributed with respect to the Sato–Tate measure `(2/π) sin²θ dθ`
on `[0, π]`, in the sense that averages of bounded continuous test functions over the primes
`p < X` converge, as `X → ∞`, to the integral against the Sato–Tate measure.

For a non-CM elliptic curve over `ℚ` (with `a p` its trace of Frobenius at `p`) this is the
Sato–Tate theorem of Clozel–Harris–Shepherd-Barron–Taylor. -/
def SatoTateLaw (θ : ℕ → ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ,
    Tendsto (fun X : ℕ => (∑ p ∈ Nat.primesBelow X, f (θ p)) / ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 (∫ θ' in (0:ℝ)..Real.pi, 2 / Real.pi * Real.sin θ' ^ 2 * f θ'))

theorem eventually_primesBelow_card_ne_zero :
    ∀ᶠ (X : ℕ) in atTop, (Nat.primesBelow X).card ≠ 0 := by
  filter_upwards [eventually_ge_atTop 3] with X hX
  exact Finset.card_ne_zero_of_mem (Nat.mem_primesBelow.2 ⟨by omega, Nat.prime_two⟩)

/-- The Sato–Tate law is exactly the statement that the empirical distributions of the angles
`θ p`, `p < X` prime, converge weakly to the Sato–Tate measure as `X → ∞`. -/
theorem satoTateLaw_iff_tendsto (θ : ℕ → ℝ) :
    SatoTateLaw θ ↔ Tendsto (fun X : ℕ => angleEmpiricalProb θ X) atTop (𝓝 satoTateProb) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine forall_congr' (fun f => ?_)
  have hEq : ∀ᶠ (X : ℕ) in atTop,
      (∑ p ∈ Nat.primesBelow X, f (θ p)) / ((Nat.primesBelow X).card : ℝ)
        = ∫ x, f x ∂((angleEmpiricalProb θ X : Measure ℝ)) := by
    filter_upwards [eventually_primesBelow_card_ne_zero] with X hX
    exact (angleEmpirical_integral θ X hX f).symm
  rw [show ∫ x, f x ∂((satoTateProb : Measure ℝ)) = ∫ x, f x ∂satoTateMeasure from rfl,
    satoTate_integral f]
  exact tendsto_congr' hEq

theorem tendsto_angleEmpiricalProb (θ : ℕ → ℝ) (h : SatoTateLaw θ) :
    Tendsto (fun X : ℕ => angleEmpiricalProb θ X) atTop (𝓝 satoTateProb) :=
  (satoTateLaw_iff_tendsto θ).1 h

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `a : ℕ → ℤ` be the traces of Frobenius of an elliptic curve over `ℚ` without complex
multiplication, and let `θ_p = arccos (a p / (2√p)) ∈ [0, π]` be the associated Frobenius
angles. Granting the Sato–Tate law (the equidistribution statement proved by
Clozel–Harris–Shepherd-Barron–Taylor for such curves), for every subinterval `[α, β]` of
`[0, π]` the proportion of primes `p < X` whose Frobenius angle lies in `[α, β]` converges,
as `X → ∞`, to the Sato–Tate mass

`(2/π) ∫_α^β sin²θ dθ = (sin α cos α - sin β cos β + β - α)/π`. -/
theorem sato_tate (a : ℕ → ℤ) (hST : SatoTateLaw (frobAngle a))
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi) :
    Tendsto (fun X : ℕ =>
        (((Nat.primesBelow X).filter (fun p => frobAngle a p ∈ Set.Icc α β)).card : ℝ) /
          ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 ((Real.sin α * Real.cos α - Real.sin β * Real.cos β + β - α) / Real.pi)) := by
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_angleEmpiricalProb (frobAngle a) hST) (E := Set.Icc α β) (satoTate_frontier_Icc α β)
  rw [show ((satoTateProb : Measure ℝ)) = satoTateMeasure from rfl, satoTate_Icc hα hαβ hβ] at key
  have key' := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp key
  rw [ENNReal.toReal_ofReal (satoTateMass_nonneg hαβ)] at key'
  refine key'.congr' ?_
  filter_upwards [eventually_primesBelow_card_ne_zero] with X hX
  simp only [Function.comp_apply]
  rw [show ((angleEmpiricalProb (frobAngle a) X : Measure ℝ)) = angleEmpirical (frobAngle a) X
      from rfl, angleEmpirical_apply _ X hX measurableSet_Icc, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  congr! 3
  exact Finset.filter_congr_decidable _ _ _

end Math2

