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

def stepA (s : Aux G.N) (b : Option Bool) (t : Aux G.N) : Prop :=
  -- T1: enter the inner loop for the vertex `v`
  (s.ph = Phase.O ∧ (s.v : ℕ) < G.N ∧ t.ph = Phase.I ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = 0 ∧ (t.c : ℕ) = 0 ∧ t.flag = false)
  ∨ -- T2: the round `i` is finished; start round `i+1`
  (s.ph = Phase.O ∧ (s.v : ℕ) = G.N ∧ (s.i : ℕ) < G.N ∧ t.ph = Phase.O ∧
      (t.i : ℕ) = (s.i : ℕ) + 1 ∧ (t.r : ℕ) = (s.cnt : ℕ) ∧ (t.v : ℕ) = 0 ∧ (t.cnt : ℕ) = 0)
  ∨ -- T3: all rounds are finished; enter the final loop
  (s.ph = Phase.O ∧ (s.i : ℕ) = G.N ∧ t.ph = Phase.F ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = 0 ∧ (t.c : ℕ) = 0)
  ∨ -- T4: skip the vertex `u` in the inner loop
  (s.ph = Phase.I ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.I ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag)
  ∨ -- T5: claim that `u` is reachable in `i` steps and start guessing a path
  (s.ph = Phase.I ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.W ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag ∧
      (t.w : ℕ) = G.st0 ∧ (t.d : ℕ) = 0)
  ∨ -- T6: follow an edge of the guessed path
  (s.ph = Phase.W ∧ (s.d : ℕ) < (s.i : ℕ) ∧ t.ph = Phase.W ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag ∧
      (t.d : ℕ) = (s.d : ℕ) + 1 ∧ G.Ed b (s.w : ℕ) (t.w : ℕ))
  ∨ -- T7: stay where we are (a shorter path is also a path)
  (s.ph = Phase.W ∧ (s.d : ℕ) < (s.i : ℕ) ∧ t.ph = Phase.W ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag ∧
      (t.d : ℕ) = (s.d : ℕ) + 1 ∧ (t.w : ℕ) = (s.w : ℕ))
  ∨ -- T8: the path reached `u`; count it and test whether it witnesses `v`
  (s.ph = Phase.W ∧ (s.w : ℕ) = (s.u : ℕ) ∧ t.ph = Phase.I ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ) + 1 ∧
      (t.flag = true ↔ (s.flag = true ∨ (s.u : ℕ) = (s.v : ℕ) ∨ G.Ed b (s.u : ℕ) (s.v : ℕ))))
  ∨ -- T9: the inner loop is finished and all vertices were counted
  (s.ph = Phase.I ∧ (s.u : ℕ) = G.N ∧ (s.c : ℕ) = (s.r : ℕ) ∧ t.ph = Phase.O ∧
      (t.i : ℕ) = (s.i : ℕ) ∧ (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) + 1 ∧
      (t.cnt : ℕ) = (s.cnt : ℕ) + (if s.flag then 1 else 0))
  ∨ -- T10: skip `u` in the final loop
  (s.ph = Phase.F ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.F ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ))
  ∨ -- T11: claim that `u` is reachable and start guessing a path
  (s.ph = Phase.F ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.WF ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ (t.w : ℕ) = G.st0 ∧ (t.d : ℕ) = 0)
  ∨ -- T12: follow an edge of the guessed path
  (s.ph = Phase.WF ∧ (s.d : ℕ) < G.N ∧ t.ph = Phase.WF ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ (t.d : ℕ) = (s.d : ℕ) + 1 ∧
      G.Ed b (s.w : ℕ) (t.w : ℕ))
  ∨ -- T13: stay where we are
  (s.ph = Phase.WF ∧ (s.d : ℕ) < G.N ∧ t.ph = Phase.WF ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ (t.d : ℕ) = (s.d : ℕ) + 1 ∧
      (t.w : ℕ) = (s.w : ℕ))
  ∨ -- T14: the path reached `u`, which is not accepting; count it
  (s.ph = Phase.WF ∧ (s.w : ℕ) = (s.u : ℕ) ∧ ¬ G.accV (s.u : ℕ) ∧ t.ph = Phase.F ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ) + 1)
  ∨ -- T15: all reachable vertices have been seen and none of them accepts
  (s.ph = Phase.F ∧ (s.u : ℕ) = G.N ∧ (s.c : ℕ) = (s.r : ℕ) ∧ t.ph = Phase.A)

/-- A state in the outer loop. -/
