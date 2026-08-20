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

lemma card_RSet (i : ℕ) : (RSet G x i).card = G.cnt x i G.N := rfl

/-- A set of `G.cnt x i G.N` vertices reachable in `i` steps is the set of *all* vertices
reachable in `i` steps.  This is the heart of the inductive counting argument. -/
