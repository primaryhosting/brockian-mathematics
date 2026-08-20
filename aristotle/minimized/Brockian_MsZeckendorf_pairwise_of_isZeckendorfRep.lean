import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/

lemma pairwise_of_isZeckendorfRep {l : List ℕ} (hl : l.IsZeckendorfRep) :
    (l ++ [0]).Pairwise (fun a b ↦ b + 2 ≤ a) := by
  rw [← List.isChain_iff_pairwise]
  exact hl

/-- In a strictly decreasing (by steps of at least `2`) list, no element is the successor of
another one. -/
