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

def AcceptsWithin (O : Oracle) (p : Prog) (x cert : Str) (T : ℕ) : Prop :=
  ∃ c' n qs, n ≤ T ∧ Prog.Exec O p (initCfg x cert) c' n qs ∧ c'.regs 1 = [true]

/-- `p` halts on `x` with guess string `cert` within `T` steps under oracle `O`. -/
