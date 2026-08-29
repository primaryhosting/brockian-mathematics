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

def queryProg (i m : ℕ) : Prog :=
  Prog.seq (padProg m)
  (Prog.seq (Prog.clear 2)
  (Prog.seq (Prog.appendReg 2 4)
  (Prog.seq (Prog.appendBit 2 false)
  (Prog.seq (appendConst 2 (List.replicate i true))
  (Prog.seq (Prog.appendBit 2 false)
  (Prog.seq (Prog.appendReg 2 0) (Prog.query 1 2)))))))

