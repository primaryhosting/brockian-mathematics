/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## Setting

We work in three-dimensional configuration space.  A many-body fermionic state is
described here by the two quantities that enter the Lieb–Thirring argument:

* its total kinetic energy `T = ⟨Ψ, (-Δ₁ - ⋯ - Δ_N) Ψ⟩`,
* its one-body density `ρ`, normalised by `∫ ρ = N`.

The deep analytic input of the theory — the Lieb–Thirring inequality at `γ = 1` in
dimension `3` — is recorded as the predicate `LiebThirringBound`.  It is stated in
its *variational* form, which is the form in which it is used, and which is
equivalent to the eigenvalue-sum formulation by the min–max principle: for every
external potential `V`, the energy of the state in `-Δ + V` is bounded below by
`- L ∫ V₋^{5/2}`.

Everything below this input is proved here:

* `legendre_pointwise` — the pointwise Legendre/Young inequality, obtained from
  Mathlib's `Real.young_inequality` for the Hölder-conjugate pair `(5/2, 5/3)`;
* `kinetic_energy_bound` — the duality passage to the Thomas–Fermi-type kinetic
  energy inequality `T ≥ K_L ∫ ρ^{5/3}`, with the explicit constant
  `K_L = (3/5)(2/(5L))^{2/3}`;
* `liebThirringBound_of_kinetic` — the converse, showing that the two forms are in
  fact equivalent (so the hypothesis is not vacuous);
* `integral_rpow_four_thirds_le` — the Hölder interpolation
  `∫ ρ^{4/3} ≤ (∫ρ)^{1/2} (∫ρ^{5/3})^{1/2}`, obtained from Mathlib's
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`;
* `lieb_thirring_stability` — stability of matter of the second kind,
  `E ≥ -C·(N + K)`.
-/

/-- Configuration space of a single particle: three-dimensional Euclidean space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- The negative part `V₋ = max (-V) 0` of a potential (a nonnegative function). -/

theorem exists_nontrivial_liebThirring_state {L : ℝ} (hL : 0 < L) :
    ∃ (ρ : Space → ℝ) (T : ℝ),
      (∀ x, 0 ≤ ρ x) ∧ (∃ x, 0 < ρ x) ∧
      AEStronglyMeasurable ρ volume ∧ Integrable ρ ∧
      Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)) ∧
      (∫ x, ρ x) = 1 ∧ LiebThirringBound L T ρ := by
  set B : Set Space := Metric.ball 0 1 with hB
  have hmB : MeasurableSet B := measurableSet_ball
  have h1 : 0 < volume B := Metric.measure_ball_pos volume 0 one_pos
  have h2 : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hv : 0 < volume.real B := ENNReal.toReal_pos h1.ne' h2
  set k : ℝ := (volume.real B)⁻¹ with hk
  have hkpos : 0 < k := by positivity
  set ρ : Space → ℝ := Set.indicator B (fun _ => k) with hρ
  have hint : (∫ x, ρ x) = 1 := by
    rw [hρ, integral_indicator_const k hmB, smul_eq_mul, hk]
    field_simp
  have hpow : ∀ p : ℝ, p ≠ 0 →
      (fun x => ρ x ^ p) = Set.indicator B (fun _ => k ^ p) := by
    intro p hp
    funext x
    rw [hρ]
    by_cases hx : x ∈ B
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, Real.zero_rpow hp]
  have hgen : ∀ c : ℝ, Integrable (Set.indicator B (fun _ => c)) := by
    intro c
    refine IntegrableOn.integrable_indicator ?_ hmB
    haveI : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top h2⟩
    exact integrable_const c
  have hI1 : Integrable ρ := hgen k
  have hI53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)) := by
    rw [hpow _ (by norm_num)]; exact hgen _
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x =>
    Set.indicator_nonneg (fun _ _ => hkpos.le) x
  refine ⟨ρ, ltKineticConst L * ∫ x, ρ x ^ ((5 : ℝ) / 3), hρ0, ⟨0, ?_⟩,
    hI1.aestronglyMeasurable, hI1, hI53, hint,
    liebThirringBound_of_kinetic hL hρ0 hI53 le_rfl⟩
  rw [hρ, Set.indicator_of_mem (by simp [hB] : (0 : Space) ∈ B)]
  exact hkpos

/-!
## Step 2: Hölder interpolation
-/

/-- Interpolation `∫ ρ^{4/3} ≤ (∫ ρ)^{1/2} (∫ ρ^{5/3})^{1/2}`: the Cauchy–Schwarz
case of Hölder's inequality (Mathlib's
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`) applied to the factorisation
`ρ^{4/3} = ρ^{1/2} · ρ^{5/6}`. -/
