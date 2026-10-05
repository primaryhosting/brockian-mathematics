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

lemma homogeneousMeasure_coset (v : ℝ × ℝ) (x : Torus) :
    homogeneousMeasure v x ((fun h => x + h) '' (H v : Set Torus)) = 1 := by
  rw [homogeneousMeasure, Measure.map_apply (measurable_cosetMap v x)
    (isClosed_coset v x).measurableSet]
  have : (fun h : ↑(H v) => x + (h : Torus)) ⁻¹' ((fun h => x + h) '' (H v : Set Torus))
      = Set.univ := by
    ext h
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact ⟨(h : Torus), h.2, rfl⟩
  rw [this, measure_univ]

