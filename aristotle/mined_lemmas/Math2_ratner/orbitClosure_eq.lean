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

lemma orbitClosure_eq (v : ℝ × ℝ) (x : Torus) :
    closure (Set.range fun t : ℝ => x + unipotentFlow v t)
      = (fun h => x + h) '' (H v : Set Torus) := by
  have hrange : (Set.range fun t : ℝ => x + unipotentFlow v t)
      = (fun h => x + h) '' (Set.range (unipotentFlow v)) := by
    ext y; constructor
    · rintro ⟨t, rfl⟩; exact ⟨unipotentFlow v t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
  rw [hrange, coe_H]
  exact ((Homeomorph.addLeft x).image_closure _).symm

/-! ## Invariant measures -/

/-- The set of translations preserving a probability measure on the torus is closed. -/
