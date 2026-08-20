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

lemma rank_id_tensor [Fintype X] [Fintype R] [DecidableEq R]
    (σ : Matrix X X ℂ) (T : Matrix (R × X) (R × X) ℂ)
    (hT : ∀ i j x x', T (i, x) (j, x') = (if i = j then (1 : ℂ) else 0) * σ x x') :
    T.rank = Fintype.card R * σ.rank := by
  have key : LinearMap.range T.mulVecLin = piSub R (LinearMap.range σ.mulVecLin) := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩ i
      refine ⟨fun x' => u (i, x'), ?_⟩
      ext x
      simp only [mulVecLin_apply, mulVec, dotProduct]
      rw [Fintype.sum_prod_type]
      simp [hT]
    · intro v hv
      choose w hw using hv
      refine ⟨fun p => w p.1 p.2, ?_⟩
      ext p
      obtain ⟨i, x⟩ := p
      simp only [mulVecLin_apply, mulVec, dotProduct]
      rw [Fintype.sum_prod_type]
      have hsum : ∀ j, ∑ x', T (i, x) (j, x') * w j x' =
          if j = i then (σ.mulVecLin (w i)) x else 0 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [hT, mulVec, dotProduct]
        · simp [hT, Ne.symm hj, hj]
      rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_ite_eq' Finset.univ i]
      simp [hw i]
  calc T.rank = finrank ℂ (LinearMap.range T.mulVecLin) := rfl
    _ = finrank ℂ (piSub R (LinearMap.range σ.mulVecLin)) := by rw [key]
    _ = Fintype.card R * σ.rank := finrank_piSub _

