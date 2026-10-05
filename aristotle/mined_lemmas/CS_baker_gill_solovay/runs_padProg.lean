import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem runs_padProg (O : Oracle) (m : ℕ) (r : Regs) :
    ∃ r' : Regs, Runs O (padProg m) r r' (padCost m (r 0).length) ∧
      r' 4 = List.replicate (((r 0).length + 2) ^ m) true ∧
      r' 0 = r 0 ∧ r' 1 = r 1 ∧ r' 2 = r 2 := by
  induction m with
  | zero =>
      obtain ⟨r1, e1, v1, o1⟩ := step_clear O r 4
      obtain ⟨r2, e2, v2, o2⟩ := step_appendBit O r1 4 true
      refine ⟨r2, (e1.seq e2).mono (by simp [padCost]), ?_, ?_, ?_, ?_⟩
      · rw [v2, v1]; simp
      · rw [o2 0 (by decide), o1 0 (by decide)]
      · rw [o2 1 (by decide), o1 1 (by decide)]
      · rw [o2 2 (by decide), o1 2 (by decide)]
  | succ m ih =>
      obtain ⟨r1, e1, v1, u0, u1, u2⟩ := ih
      obtain ⟨r2, e2, v2, w0, w1, w2⟩ :=
        runs_mulBlock O r1 (((r 0).length + 2) ^ m) v1
      refine ⟨r2, (e1.seq e2).mono ?_, ?_, ?_, ?_, ?_⟩
      · rw [u0]
        simp only [padCost]
        have : ((r 0).length + 2) ^ m + 1 ≤ ((r 0).length + 2) ^ m + 1 := le_rfl
        nlinarith [Nat.zero_le (((r 0).length + 2) ^ m)]
      · rw [v2, u0, ← pow_succ']
      · rw [w0, u0]
      · rw [w1, u1]
      · rw [w2, u2]

end CS

import RequestProject.Gadgets

/-!
# The nondeterministic program used for the second oracle

`guessProg` guesses a string `w` of the same length as its input and queries the
oracle about `w`.
-/

namespace CS

open Prog

/-- `while r3 ≠ [] do (guess a bit into r2; pop r3)`. -/
