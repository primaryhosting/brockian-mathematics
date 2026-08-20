import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/

lemma two_le_of_mem_zeckendorf {l : List ℕ} (hl : l.IsZeckendorfRep) {i : ℕ} (hi : i ∈ l) :
    2 ≤ i := by
  have h := pairwise_of_isZeckendorfRep hl
  rw [List.pairwise_append] at h
  simpa using h.2.2 i hi 0 (by simp)

/-- A Zeckendorf representation has no duplicates. -/
