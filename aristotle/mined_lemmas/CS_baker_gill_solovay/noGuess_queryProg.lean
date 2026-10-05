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

theorem noGuess_queryProg (i m : ℕ) : noGuess (queryProg i m) := by
  refine ⟨noGuess_padProg m, trivial, trivial, trivial, ?_, trivial, trivial, trivial⟩
  exact noGuess_appendConst 2 (List.replicate i true)

/-- The exact cost of `queryProg i m` on inputs of length `n`. -/
