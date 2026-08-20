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

def InvW (i r v cnt u c : ℕ) (flag : Bool) (w d : ℕ) : Prop :=
  i ≤ G.N ∧ r = G.cnt x i G.N ∧ v < G.N ∧ cnt = G.cnt x (i + 1) v ∧ u < G.N ∧
    InnerOK G x i u c v flag ∧ d ≤ i ∧ G.Rch x d w

/-- Invariant of the final loop. -/
