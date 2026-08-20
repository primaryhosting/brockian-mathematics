import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/

lemma not_mem_succ_of_pairwise {l : List ℕ} (h : l.Pairwise (fun a b ↦ b + 2 ≤ a)) {i : ℕ}
    (hi : i ∈ l) (hj : i + 1 ∈ l) : False := by
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hi with rfl | hi'
    · rcases List.mem_cons.1 hj with hcon | hj'
      · omega
      · have := h.1 _ hj'; omega
    · rcases List.mem_cons.1 hj with rfl | hj'
      · have := h.1 _ hi'; omega
      · exact ih h.2 hi' hj'

/-- Every element of a Zeckendorf representation is at least `2`. -/
