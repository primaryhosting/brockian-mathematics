import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Nat Classical Pointwise

open MeasureTheory Topology Filter Set

namespace Math2

noncomputable section

/-! ## Setting

We work with the homogeneous space `X = G / Γ` where `G = ℝ²` is an abelian Lie group and
`Γ = ℤ²` is a lattice in it, so that `X` is the two–dimensional torus `𝕋² = ℝ²/ℤ²`.
Since `G` is abelian, every one–parameter subgroup `t ↦ t • v` of `G` is unipotent
(the adjoint representation is trivial), so the flow it induces on `X` is a unipotent flow.

This is the classical abelian model case of Ratner's theorems, containing the linear flows on
the torus with irrational slope. -/

/-- The two-dimensional torus `ℝ²/ℤ²`, the homogeneous space `G/Γ` for `G = ℝ²`, `Γ = ℤ²`. -/
abbrev Torus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `ℝ² → ℝ²/ℤ²`. -/

lemma isClosed_translationStabilizer (μ : Measure Torus) [IsProbabilityMeasure μ] :
    IsClosed {g : Torus | Measure.map (· + g) μ = μ} := by
  have key : {g : Torus | Measure.map (· + g) μ = μ}
      = ⋂ f : BoundedContinuousFunction Torus ℝ,
          {g : Torus | (∫ x, f (x + g) ∂μ) = ∫ x, f x ∂μ} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    have hmeas : Measurable (fun x : Torus => x + g) := measurable_add_const g
    haveI : IsProbabilityMeasure (Measure.map (fun x : Torus => x + g) μ) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    constructor
    · intro hg f
      have h1 : ∫ x, f x ∂(Measure.map (fun x : Torus => x + g) μ) = ∫ x, f x ∂μ := by rw [hg]
      rwa [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable] at h1
    · intro hf
      refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
      rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
      exact hf f
  rw [key]
  refine isClosed_iInter fun f => ?_
  have hcont : Continuous fun g : Torus => ∫ x, f (x + g) ∂μ :=
    continuous_of_dominated (bound := fun _ => ‖f‖)
      (fun g => (f.continuous.comp (continuous_add_right g)).aestronglyMeasurable)
      (fun g => Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _)
      (integrable_const _)
      (Filter.Eventually.of_forall fun x =>
        f.continuous.comp (continuous_const.add continuous_id))
  exact isClosed_eq hcont continuous_const

/-- **Ratner measure classification** (abelian case): a probability measure invariant under the
unipotent flow is automatically invariant under the whole closed connected subgroup `H`, i.e. it
is homogeneous along `H`. -/
