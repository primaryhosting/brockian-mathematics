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

theorem polyBdd_padCost (m : ℕ) : PolyBdd (fun n => padCost m n) := by
  induction m with
  | zero => exact polyBdd_const 2
  | succ m ih =>
      refine polyBdd_add ih ?_
      refine polyBdd_mul (polyBdd_mul (polyBdd_const 8) (polyBdd_shift 1)) ?_
      exact polyBdd_add (polyBdd_pow (polyBdd_shift 2) m) (polyBdd_const 1)

