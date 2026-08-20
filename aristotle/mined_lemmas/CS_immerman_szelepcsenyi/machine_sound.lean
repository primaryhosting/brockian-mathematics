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

theorem machine_sound (h : (machine G).Accepts x) : ¬ ∃ q, G.accV q ∧ G.Reachable x q := by
  obtain ⟨q, hq, hpath⟩ := h
  have hinv : Inv G x q := inv_reachable hpath inv_start
  rw [Inv_A hq] at hinv
  rintro ⟨p, hp, hpr⟩
  exact hinv ⟨p, hp, (Rch_iff_reachable p).2 hpr⟩

end IS
end CS

import RequestProject.Reach

/-!
# The inductive counting machine

Given a configuration graph (vertices `< N`, start vertex `st0`, edge relation `Ed`,
accepting vertices `accV`) we build a nondeterministic branching program which accepts an
input `x` **iff** no accepting vertex is reachable in the configuration graph on `x`.

The program implements the Immerman--Szelepcsényi inductive counting algorithm.
-/

open scoped Classical

namespace CS
namespace IS

/-- The phases of the counting machine. -/
inductive Phase
  /-- Outer loop: computing the set reachable in `i+1` steps. -/
  | O
  /-- Inner loop: enumerating the vertices reachable in `i` steps. -/
  | I
  /-- Verifying a guessed path (inside the inner loop). -/
  | W
  /-- Final loop: enumerating the reachable vertices and checking none accepts. -/
  | F
  /-- Verifying a guessed path (inside the final loop). -/
  | WF
  /-- The accepting phase. -/
  | A
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{Phase.O, Phase.I, Phase.W, Phase.F, Phase.WF, Phase.A}, by intro p; cases p <;> decide⟩

