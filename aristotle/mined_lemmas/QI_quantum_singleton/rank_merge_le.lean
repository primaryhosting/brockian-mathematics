import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

lemma rank_merge_le [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq Z]
    (M : Matrix (Z × X) Y ℂ) (N : Matrix X (Z × Y) ℂ)
    (h : ∀ z x y, N x (z, y) = M (z, x) y) :
    M.rank ≤ Fintype.card Z * N.rank := by
  have hsub : LinearMap.range M.mulVecLin ≤ piSub Z (LinearMap.range N.mulVecLin) := by
    rintro _ ⟨u, rfl⟩ z
    refine ⟨fun p => if p.1 = z then u p.2 else 0, ?_⟩
    ext x
    simp only [mulVecLin_apply, mulVec, dotProduct]
    rw [Fintype.sum_prod_type]
    simp [h, Finset.sum_ite_eq' Finset.univ z]
  calc M.rank = finrank ℂ (LinearMap.range M.mulVecLin) := rfl
    _ ≤ finrank ℂ (piSub Z (LinearMap.range N.mulVecLin)) := Submodule.finrank_mono hsub
    _ = Fintype.card Z * N.rank := finrank_piSub _

/-- The rank of `1 ⊗ σ` is `(card R) * rank σ`. -/
