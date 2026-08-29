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

theorem exists_oracle_P_eq_NP : ∃ A : Oracle, PClass A = NPClass A :=
  ⟨oracleA, Set.Subset.antisymm (PClass_subset_NPClass oracleA)
    NPClass_oracleA_subset_PClass⟩

end CS

import RequestProject.Model

/-!
# Programming gadgets

Concrete programs of the model of `RequestProject.Model`, together with their
behaviour and running time.
-/

namespace CS

open Prog

/-- `Runs O p r r' T`: from register file `r`, the program `p` terminates with
register file `r'`, asking no oracle queries, at cost at most `T` (for every
value of the guess string, which is left untouched). -/
