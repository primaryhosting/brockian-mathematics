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

theorem integral_rpow_four_thirds_le {ρ : Space → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hmeas : AEStronglyMeasurable ρ volume) (hint1 : Integrable ρ)
    (hint53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3))) :
    ∫ x, ρ x ^ ((4 : ℝ) / 3) ≤
      Real.sqrt (∫ x, ρ x) * Real.sqrt (∫ x, ρ x ^ ((5 : ℝ) / 3)) := by
  have hcj : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hfm : AEStronglyMeasurable (fun x => ρ x ^ ((1 : ℝ) / 2)) volume :=
    (hmeas.aemeasurable.pow_const _).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => ρ x ^ ((5 : ℝ) / 6)) volume :=
    (hmeas.aemeasurable.pow_const _).aestronglyMeasurable
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hfL : MemLp (fun x => ρ x ^ ((1 : ℝ) / 2)) (ENNReal.ofReal 2) volume := by
    rw [h2, MeasureTheory.memLp_two_iff_integrable_sq hfm]
    have h : ∀ x, (ρ x ^ ((1 : ℝ) / 2)) ^ 2 = ρ x := by
      intro x
      rw [← Real.rpow_natCast (ρ x ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul (hρ0 x)]
      norm_num
    simpa only [h] using hint1
  have hgL : MemLp (fun x => ρ x ^ ((5 : ℝ) / 6)) (ENNReal.ofReal 2) volume := by
    rw [h2, MeasureTheory.memLp_two_iff_integrable_sq hgm]
    have h : ∀ x, (ρ x ^ ((5 : ℝ) / 6)) ^ 2 = ρ x ^ ((5 : ℝ) / 3) := by
      intro x
      rw [← Real.rpow_natCast (ρ x ^ ((5 : ℝ) / 6)) 2, ← Real.rpow_mul (hρ0 x)]
      norm_num
    simpa only [h] using hint53
  have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hcj
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hρ0 x) ((1 : ℝ) / 2))
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hρ0 x) ((5 : ℝ) / 6))
    hfL hgL
  have e1 : ∀ x, ρ x ^ ((1 : ℝ) / 2) * ρ x ^ ((5 : ℝ) / 6) = ρ x ^ ((4 : ℝ) / 3) := by
    intro x; rw [← Real.rpow_add' (hρ0 x) (by norm_num)]; norm_num
  have e2 : ∀ x, (ρ x ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = ρ x := by
    intro x; rw [← Real.rpow_mul (hρ0 x)]; norm_num
  have e3 : ∀ x, (ρ x ^ ((5 : ℝ) / 6)) ^ (2 : ℝ) = ρ x ^ ((5 : ℝ) / 3) := by
    intro x; rw [← Real.rpow_mul (hρ0 x)]; norm_num
  simp only [e1, e2, e3] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact key

/-!
## Step 3: the elementary optimisation
-/

/-- `k t - c √t ≥ - c²/(4k)` for `k > 0`, `t ≥ 0`. -/
