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

def mkWF (r u c w d : ℕ) : Aux G.N :=
  { ph := Phase.WF, i := fv G.N 0, r := fv G.N r, v := fv G.N 0, cnt := fv G.N 0,
    u := fv G.N u, c := fv G.N c, w := fv G.N w, d := fv G.N d, flag := false }

/-- The accepting state. -/
