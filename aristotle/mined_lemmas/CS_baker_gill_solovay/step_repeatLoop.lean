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

theorem step_repeatLoop (O : Oracle) (r : Regs) {ctr src dst : ℕ} (hcs : ctr ≠ src)
    (hcd : ctr ≠ dst) (hsd : src ≠ dst) (a : ℕ) (hsrc : r src = List.replicate a true) :
    ∃ r' : Regs, Runs O (repeatLoop ctr src dst) r r' ((r ctr).length * (3 + a) + 1) ∧
      r' dst = r dst ++ List.replicate ((r ctr).length * a) true ∧ r' ctr = [] ∧
      ∀ j, j ≠ ctr → j ≠ dst → r' j = r j := by
  refine ⟨Function.update (Function.update r dst
      (r dst ++ List.replicate ((r ctr).length * a) true)) ctr [],
    runs_repeatLoop hcs hcd hsd a (r ctr) r rfl hsrc, ?_, by simp, fun j h1 h2 => ?_⟩
  · simp [Function.update_apply, Ne.symm hcd]
  · simp [Function.update_apply, h1, h2]

/-! ### Building a long pad -/

/-- Multiplies the length of register `4` by `|r 0| + 2` (registers `3`, `5` are
scratch). -/
