import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

def mkI (i r v cnt u c : ℕ) (flag : Bool) : Aux G.N :=
  { ph := Phase.I, i := fv G.N i, r := fv G.N r, v := fv G.N v, cnt := fv G.N cnt,
    u := fv G.N u, c := fv G.N c, w := fv G.N G.st0, d := fv G.N 0, flag := flag }

/-- A state verifying a guessed path inside the inner loop. -/
