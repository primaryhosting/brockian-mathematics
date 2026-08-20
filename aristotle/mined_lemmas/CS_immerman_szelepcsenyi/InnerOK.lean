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

def InnerOK (i u c v : ℕ) (flag : Bool) : Prop :=
  ∃ S : Finset ℕ, (∀ y ∈ S, y < u ∧ G.Rch x i y) ∧ S.card = c ∧
    (flag = true → G.Rch x (i + 1) v) ∧
    (flag = false → ∀ y ∈ S, ¬ (y = v ∨ G.edg x y v))

/-- The invariant of the final loop: the vertices counted so far form a set `S` of reachable
vertices `< u`, none of which is accepting. -/
