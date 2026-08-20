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

lemma ext_emb (y : Q d) (j : Fin d) : ext T hd y (emb T hd j) = y j := by
  unfold ext
  rw [dif_pos (emb_mem T hd j)]
  congr 1
  have : (⟨emb T hd j, emb_mem T hd j⟩ : {x // x ∈ T}) = (T.orderIsoOfFin hd) j := rfl
  rw [this, OrderIso.symm_apply_apply]

