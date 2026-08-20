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

lemma image_emb_univ : (univ : Finset (Fin d)).image (emb T hd) = T := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hi
    exact emb_mem T hd j
  · intro hi
    obtain ⟨j, rfl⟩ := exists_emb_eq T hd hi
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩

