import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/

theorem zeckendorf_exists (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℕ, (∀ i ∈ S, 2 ≤ i) ∧ (∀ i ∈ S, i + 1 ∉ S) ∧
      ∑ i ∈ S, Nat.fib i = n := by
  classical
  obtain ⟨l, hl, hsum⟩ : ∃ l : List ℕ, l.IsZeckendorfRep ∧ (l.map Nat.fib).sum = n :=
    ⟨Nat.zeckendorf n, Nat.isZeckendorfRep_zeckendorf n, Nat.sum_zeckendorf_fib n⟩
  refine ⟨l.toFinset, ?_, ?_, ?_⟩
  · intro i hi
    exact two_le_of_mem_zeckendorf hl (List.mem_toFinset.1 hi)
  · intro i hi h
    exact no_consecutive_of_isZeckendorfRep hl (List.mem_toFinset.1 hi) (List.mem_toFinset.1 h)
  · rw [← hsum]
    exact List.sum_toFinset _ (nodup_of_isZeckendorfRep hl)

end Brockian.MsZeckendorf

