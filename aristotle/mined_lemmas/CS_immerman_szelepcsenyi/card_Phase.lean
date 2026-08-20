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

lemma card_Phase : Fintype.card Phase = 6 := rfl

/-- A state of the counting machine: a phase together with a bounded number of counters,
each of which is at most `N + 1`. -/
structure Aux (N : ℕ) where
  /-- current phase -/
  ph : Phase
  /-- round number -/
  i : Fin (N + 2)
  /-- the (verified) number of vertices reachable in at most `i` steps -/
  r : Fin (N + 2)
  /-- outer loop variable -/
  v : Fin (N + 2)
  /-- number of vertices `< v` reachable in at most `i+1` steps -/
  cnt : Fin (N + 2)
  /-- inner loop variable -/
  u : Fin (N + 2)
  /-- number of vertices found so far in the inner loop -/
  c : Fin (N + 2)
  /-- current vertex of the guessed path -/
  w : Fin (N + 2)
  /-- length of the guessed path so far -/
  d : Fin (N + 2)
  /-- has a witness for `v` been found? -/
  flag : Bool

/-- Encoding of states, used only to bound their number. -/
