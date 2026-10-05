/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ### The `n`-fold power of a word -/

/-- `rep b n` is the `n`-fold concatenation `bⁿ` of the word `b` with itself. -/

theorem dfa_pumping {x : List α} (hx : x ∈ M.accepts) (hlen : Fintype.card σ ≤ x.length) :
    ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧
      ∀ n : ℕ, a ++ rep b n ++ c ∈ M.accepts := by
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card σ + 1) => M.evalFrom M.start (x.take i)) (by simp)
  -- We may assume `i < j`.
  wlog hlt : (i : ℕ) < (j : ℕ) generalizing i j
  · exact this j i hne.symm heq.symm
      (lt_of_le_of_ne (not_lt.1 hlt) (fun h => hne (Fin.ext h.symm)))
  have hprefix : (x.take j).take i = x.take i := by
    rw [List.take_take, min_eq_left hlt.le]
  have hab : x.take i ++ (x.take j).drop i = x.take j := by
    conv_lhs => rw [← hprefix]
    rw [List.take_append_drop]
  have hsplit : x = x.take i ++ (x.take j).drop i ++ x.drop j := by
    rw [hab, List.take_append_drop]
  -- the middle block is a loop at the state reached after reading the prefix `x.take i`
  have hloop : M.evalFrom (M.evalFrom M.start (x.take i)) ((x.take j).drop i)
      = M.evalFrom M.start (x.take i) := by
    rw [← M.evalFrom_of_append, hab, ← heq]
  refine ⟨x.take i, (x.take j).drop i, x.drop j, hsplit, ?_, ?_, ?_⟩
  · have hj : (j : ℕ) ≤ Fintype.card σ := Nat.lt_succ_iff.1 j.isLt
    simp only [List.length_take, List.length_drop]
    omega
  · have hjx : (j : ℕ) ≤ x.length := le_trans (Nat.lt_succ_iff.1 j.isLt) hlen
    intro h
    have hl := congrArg List.length h
    simp only [List.length_drop, List.length_take, List.length_nil] at hl
    omega
  · intro n
    have hfin : M.evalFrom (M.evalFrom M.start (x.take i)) (x.drop j)
        = M.evalFrom M.start x := by
      conv_rhs => rw [hsplit]
      rw [M.evalFrom_of_append, M.evalFrom_of_append, hloop]
    rw [DFA.mem_accepts, DFA.eval, M.evalFrom_of_append, M.evalFrom_of_append,
      evalFrom_rep M hloop, hfin]
    exact hx

/-! ### Pumping for regular languages -/

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0` such that every word `x ∈ L`
of length at least `p` can be split as `x = a ++ b ++ c` with `|a| + |b| ≤ p`, `b ≠ []`,
and `a ++ bⁿ ++ c ∈ L` for every `n : ℕ`.
-/
