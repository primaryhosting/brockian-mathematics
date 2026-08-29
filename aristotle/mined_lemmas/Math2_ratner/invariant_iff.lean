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

lemma invariant_iff (v : ℝ × ℝ) (μ : Measure Torus) (hμ : IsProbabilityMeasure μ) :
    (∀ t : ℝ, Measure.map (· + unipotentFlow v t) μ = μ) ↔
      (∀ h ∈ H v, Measure.map (· + h) μ = μ) := by
  haveI := hμ
  constructor
  · intro hinv h hh
    have hsub : (H v : Set Torus) ⊆ {g : Torus | Measure.map (· + g) μ = μ} := by
      rw [coe_H]
      exact (isClosed_translationStabilizer μ).closure_subset_iff.mpr
        (by rintro - ⟨t, rfl⟩; exact hinv t)
    exact hsub hh
  · intro hH t
    exact hH _ (flow_mem_H v t)

/-! ## The homogeneous measure on a closed orbit -/

instance instCompactSpaceH (v : ℝ × ℝ) : CompactSpace ↑(H v) :=
  isCompact_iff_compactSpace.mp (isClosed_H v).isCompact

/-- The Haar probability measure of the compact group `H v`. -/
