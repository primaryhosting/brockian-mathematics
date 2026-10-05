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

lemma zero_mem_fiber {a : ℝ} (ha : Irrational a) (w : AddCircle (1:ℝ)) :
    ((0 : AddCircle (1:ℝ)), w) ∈ H (1, a) := by
  have hdense : DenseRange (fun n : ℤ => n • ((a : AddCircle (1:ℝ)))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using ha)
  have hphi : Continuous (fun u : AddCircle (1:ℝ) => ((0 : AddCircle (1:ℝ)), u)) :=
    continuous_const.prodMk continuous_id
  have hsub : (fun u : AddCircle (1:ℝ) => ((0 : AddCircle (1:ℝ)), u)) ''
      (Set.range (fun n : ℤ => n • ((a : AddCircle (1:ℝ))))) ⊆ (H (1, a) : Set Torus) := by
    rintro - ⟨-, ⟨n, rfl⟩, rfl⟩
    show ((0 : AddCircle (1:ℝ)), n • ((a : AddCircle (1:ℝ)))) ∈ (H (1, a) : Set Torus)
    have h1 : ((0 : AddCircle (1:ℝ)), n • ((a : AddCircle (1:ℝ))))
        = unipotentFlow (1, a) (n : ℝ) := by
      rw [flow_eq, coe_int_zero n, ← zsmul_eq_mul, QuotientAddGroup.mk_zsmul]
    rw [h1]
    exact flow_mem_H _ _
  have hmem : ((0 : AddCircle (1:ℝ)), w) ∈ closure ((fun u : AddCircle (1:ℝ) =>
      ((0 : AddCircle (1:ℝ)), u)) '' (Set.range (fun n : ℤ => n • ((a : AddCircle (1:ℝ)))))) := by
    apply image_closure_subset_closure_image hphi
    exact ⟨w, hdense w, rfl⟩
  have hcl := closure_mono hsub hmem
  rwa [(isClosed_H (1, a)).closure_eq] at hcl

/-- For an irrational slope `α`, the group `H` attached to the direction `(1, α)` is everything. -/
