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

def guessProg : Prog :=
  Prog.seq (Prog.clear 3)
  (Prog.seq (Prog.appendReg 3 0)
  (Prog.seq (Prog.clear 2)
  (Prog.seq guessLoop (Prog.query 1 2))))

/-- Running the guessing loop with the certificate `w`. -/
