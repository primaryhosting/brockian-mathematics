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

theorem step_appendConst (O : Oracle) (r : Regs) (i : ℕ) (s : Str) :
    ∃ r' : Regs, Runs O (appendConst i s) r r' (s.length + 1) ∧ r' i = r i ++ s ∧
      ∀ j, j ≠ i → r' j = r j := by
  refine ⟨Function.update r i (r i ++ s), runs_appendConst i s r, by simp, fun j hj => ?_⟩
  simp [Function.update_apply, hj]

