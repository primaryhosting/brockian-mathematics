import Mathlib
namespace Brockian.MsZeckendorf

open List Nat

local instance zeck_isTrans : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- A Zeckendorf representation, unfolded as a `Pairwise` statement on `l ++ [0]`. -/

lemma no_consecutive_of_isZeckendorfRep {l : List ℕ} (hl : l.IsZeckendorfRep) {i : ℕ}
    (hi : i ∈ l) : i + 1 ∉ l := by
  intro h
  have hp := pairwise_of_isZeckendorfRep hl
  rw [List.pairwise_append] at hp
  exact not_mem_succ_of_pairwise hp.1 hi h

/-- Zeckendorf's theorem (existence): every positive integer is a sum of non-consecutive
    Fibonacci numbers (indices ≥ 2, no two consecutive).

    (The positivity hypothesis `hn` is kept as stated, although the proof does not need it:
    the empty sum represents `0`.) -/
