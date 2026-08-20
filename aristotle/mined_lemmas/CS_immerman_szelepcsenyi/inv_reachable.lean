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

lemma inv_reachable {s t : Aux G.N}
    (h : Relation.ReflTransGen ((machine G).edge x) s t) (hs : Inv G x s) : Inv G x t := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact inv_step hstep ih

/-- Soundness: if the counting machine accepts `x`, then no accepting vertex of the
configuration graph is reachable. -/
