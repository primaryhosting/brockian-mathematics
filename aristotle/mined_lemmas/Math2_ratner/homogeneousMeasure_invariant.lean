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

lemma homogeneousMeasure_invariant (v : ℝ × ℝ) (x : Torus) {g : Torus} (hg : g ∈ H v) :
    Measure.map (· + g) (homogeneousMeasure v x) = homogeneousMeasure v x := by
  rw [homogeneousMeasure, Measure.map_map (measurable_add_const g) (measurable_cosetMap v x)]
  have hcomp : ((fun y : Torus => y + g) ∘ fun h : ↑(H v) => x + (h : Torus))
      = (fun h : ↑(H v) => x + (h : Torus)) ∘ (fun h : ↑(H v) => h + ⟨g, hg⟩) := by
    funext h
    simp [add_assoc]
  rw [hcomp, ← Measure.map_map (measurable_cosetMap v x) (measurable_add_const _),
    map_add_right_eq_self (haarH v) (⟨g, hg⟩ : ↑(H v))]

/-- **Uniqueness of the invariant measure on a closed orbit**: an invariant probability measure
giving full mass to the closed orbit `x + H v` is the homogeneous measure of that orbit. -/
