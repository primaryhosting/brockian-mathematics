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

lemma H_eq_top_of_irrational {a : ℝ} (ha : Irrational a) : H (1, a) = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  rintro ⟨y1, y2⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective (α := ℝ) y1
  have h1 : ((t : AddCircle (1:ℝ)), y2)
      = unipotentFlow (1, a) t + ((0 : AddCircle (1:ℝ)), y2 - ((t * a : ℝ) : AddCircle (1:ℝ))) := by
    rw [flow_eq]
    simp
  rw [h1]
  exact AddSubgroup.add_mem _ (flow_mem_H _ _) (zero_mem_fiber ha _)

/-- **Density of orbits**: for an irrational slope, every orbit of the linear flow on `𝕋²` is
dense. -/
