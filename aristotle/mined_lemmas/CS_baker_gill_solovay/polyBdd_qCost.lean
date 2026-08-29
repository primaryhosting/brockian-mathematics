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

theorem polyBdd_qCost (i m : ℕ) : PolyBdd (fun n => qCost i m n) := by
  refine polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_add (polyBdd_padCost m) ?_)
    (polyBdd_const (2 * i))) ?_) (polyBdd_const 10)
  · exact polyBdd_mul (polyBdd_const 2) (polyBdd_pow (polyBdd_shift 2) m)
  · exact polyBdd_mul (polyBdd_const 2) (polyBdd_mono (fun n => le_rfl) (polyBdd_shift 0))

/-- Behaviour of `queryProg`. -/
