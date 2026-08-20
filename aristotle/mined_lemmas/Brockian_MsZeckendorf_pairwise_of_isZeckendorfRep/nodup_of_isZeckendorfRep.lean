import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/

lemma nodup_of_isZeckendorfRep {l : List ℕ} (hl : l.IsZeckendorfRep) : l.Nodup := by
  have h := pairwise_of_isZeckendorfRep hl
  rw [List.pairwise_append] at h
  exact h.1.imp (by omega)

/-- A Zeckendorf representation contains no two consecutive numbers. -/
