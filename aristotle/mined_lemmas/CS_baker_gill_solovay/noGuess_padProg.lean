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

theorem noGuess_padProg (m : ℕ) : noGuess (padProg m) := by
  induction m with
  | zero => exact ⟨trivial, trivial⟩
  | succ m ih => exact ⟨ih, noGuess_mulBlock⟩

/-- A (crude) bound for the cost of `padProg`. -/
