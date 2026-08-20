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

lemma rank_smul_ne_zero [Fintype X] [Fintype Y] (c : ℂ) (hc : c ≠ 0) (M : Matrix X Y ℂ) :
    (c • M).rank = M.rank := by
  have h : LinearMap.range (c • M).mulVecLin = LinearMap.range M.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨c • u, by ext x; simp⟩
    · rintro _ ⟨u, rfl⟩
      refine ⟨c⁻¹ • u, ?_⟩
      ext x
      have hx : c⁻¹ * (c * (M *ᵥ u) x) = (M *ᵥ u) x := by field_simp
      simpa using hx
  simp only [Matrix.rank]
  rw [h]

