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

theorem ratner_dense_orbit {a : ℝ} (ha : Irrational a) (x : Torus) :
    closure (Set.range fun t : ℝ => x + unipotentFlow (1, a) t) = Set.univ := by
  rw [orbitClosure_eq, H_eq_top_of_irrational ha]
  ext y
  simp only [AddSubgroup.coe_top, image_univ, mem_range, mem_univ, iff_true]
  exact ⟨y - x, by abel⟩

/-- **Unique ergodicity**: for an irrational slope, the only Borel probability measure on `𝕋²`
invariant under the linear flow is the Haar (Lebesgue) measure. -/
