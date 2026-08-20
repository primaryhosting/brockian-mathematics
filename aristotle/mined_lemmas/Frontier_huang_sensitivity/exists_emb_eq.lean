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

lemma exists_emb_eq {i : Fin n} (hi : i ∈ T) : ∃ j : Fin d, emb T hd j = i := by
  refine ⟨(T.orderIsoOfFin hd).symm ⟨i, hi⟩, ?_⟩
  have : (T.orderIsoOfFin hd) ((T.orderIsoOfFin hd).symm ⟨i, hi⟩) = ⟨i, hi⟩ :=
    OrderIso.apply_symm_apply _ _
  exact congrArg Subtype.val this

