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

lemma sens_restrict_le (f : Q n → Bool) (y : Q d) :
    sens (restrict T hd f) y ≤ sens f (ext T hd y) := by
  refine Finset.card_le_card_of_injOn (emb T hd) (fun j hj => ?_)
    (fun a _ b _ h => emb_injective T hd h)
  rw [Finset.mem_coe, Finset.mem_filter] at hj
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h := hj.2
  unfold restrict at h
  rw [ext_flipAt] at h
  exact h

