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

def coNL (L : Set (List Bool)) : Prop := NL Lᶜ

end CS

import RequestProject.Soundness

/-!
# Completeness of the counting machine

If no accepting vertex of the configuration graph is reachable, then the counting machine
has an accepting run.  This is the direction which uses the actual inductive counting
algorithm: in the run we guess, for each round `i`, the set of vertices reachable in at
most `i` steps together with the certifying paths, and we check the guesses against the
previously computed cardinality.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable {G : Data} {x : List Bool}

/-- Runs of the counting machine. -/
abbrev MR (G : Data) (x : List Bool) (s t : Aux G.N) : Prop :=
  Relation.ReflTransGen ((machine G).edge x) s t

/-- Discharges the arithmetic side conditions about the fields of the states. -/
macro "mkfin" : tactic =>
  `(tactic| first
      | rfl
      | (simp only [mkO, mkI, mkW, mkF, mkWF, mkA, fv]; try omega))

