import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

set_option grind.warning false

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/

lemma isClosed_defRange [CompleteSpace H] {K : OperatorGraph H} (hKsym : IsSymmetricGraph K)
    (hKclosed : IsClosed (K : Set (H × H))) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    IsClosed ((defRange c K : Submodule ℂ H) : Set H) := by
  classical
  haveI : CompleteSpace K := hKclosed.completeSpace_coe
  set f : K → H := fun p => ((p : H × H).2 + c • (p : H × H).1) with hf
  set M : ℝ≥0 := Real.toNNReal (max 1 ‖c‖⁻¹) with hM
  have hMcoe : (M : ℝ) = max 1 ‖c‖⁻¹ :=
    Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  have hanti : AntilipschitzWith M f := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro x y
    have hmem : ((x : H × H) - (y : H × H)) ∈ K := K.sub_mem x.2 y.2
    have hle := norm_le_norm_shift hKsym hmem hc hc0
    have hEq : f x - f y = ((x : H × H) - (y : H × H)).2
        + c • ((x : H × H) - (y : H × H)).1 := by
      simp only [hf, Prod.fst_sub, Prod.snd_sub, smul_sub]
      abel
    have hdist : dist x y = ‖(x : H × H) - (y : H × H)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
    rw [hdist, dist_eq_norm, hEq, hMcoe]
    exact hle
  have huc : UniformContinuous f := by
    have hfeq : f = fun p : K => (shiftMap c) ((p : H × H)) := rfl
    rw [hfeq]
    exact (shiftMap c : (H × H) →L[ℂ] H).uniformContinuous.comp uniformContinuous_subtype_val
  have hclosedRange : IsClosed (Set.range f) := (hanti.isComplete_range huc).isClosed
  have hsets : Set.range f = ((defRange c K : Submodule ℂ H) : Set H) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact mem_defRange_iff.mpr ⟨(p : H × H), p.2, rfl⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := mem_defRange_iff.mp hz
      exact ⟨⟨p, hp⟩, rfl⟩
  rwa [hsets] at hclosedRange

