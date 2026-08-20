import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma ext_flipAt (y : Q d) (j : Fin d) :
    ext T hd (flipAt y j) = flipAt (ext T hd y) (emb T hd j) := by
  funext i
  by_cases hi : i ∈ T
  · obtain ⟨k, rfl⟩ := exists_emb_eq T hd hi
    rcases eq_or_ne k j with rfl | hkj
    · rw [ext_emb, flipAt_apply_self, flipAt_apply_self, ext_emb]
    · have hne : emb T hd k ≠ emb T hd j := fun h => hkj (emb_injective T hd h)
      rw [ext_emb, flipAt_apply_of_ne _ hkj, flipAt_apply_of_ne _ hne, ext_emb]
  · have hne : i ≠ emb T hd j := fun h => hi (h ▸ emb_mem T hd j)
    rw [ext_of_not_mem T hd _ hi, flipAt_apply_of_ne _ hne, ext_of_not_mem T hd _ hi]

