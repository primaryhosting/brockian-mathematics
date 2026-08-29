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

theorem ratner_unique_ergodicity {a : ℝ} (ha : Irrational a) (μ : Measure Torus)
    (hμ : IsProbabilityMeasure μ)
    (hinv : ∀ t : ℝ, Measure.map (· + unipotentFlow (1, a) t) μ = μ) :
    μ = (volume : Measure Torus) := by
  haveI := hμ
  have hall : ∀ g : Torus, Measure.map (· + g) μ = μ := fun g =>
    (invariant_iff (1, a) μ hμ).mp hinv g (by rw [H_eq_top_of_irrational ha]; trivial)
  haveI : μ.IsAddLeftInvariant := by
    constructor
    intro g
    have hfun : (fun x : Torus => g + x) = (fun x : Torus => x + g) := funext fun x => add_comm g x
    rw [hfun]
    exact hall g
  haveI : (volume : Measure Torus).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hvol : (volume : Measure Torus) Set.univ = 1 := by
    rw [Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, AddCircle.measure_univ]
    simp
  have h := Measure.isAddLeftInvariant_eq_smul μ (volume : Measure Torus)
  have huniv := congrArg (fun ν : Measure Torus => ν Set.univ) h
  simp only [Measure.smul_apply, hvol, measure_univ, ENNReal.smul_def, smul_eq_mul,
    mul_one] at huniv
  have hc : μ.addHaarScalarFactor (volume : Measure Torus) = 1 := by exact_mod_cast huniv.symm
  rw [h, hc, one_smul]

end

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

