/-
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

variable {α β : Type*}

/-- The neighbourhood of a left vertex `a` in the bipartite graph with adjacency
relation `Adj : α → β → Prop`: the finset of right vertices adjacent to `a`. -/

def neighbors [Fintype β] [DecidableEq β] (Adj : α → β → Prop)
    [∀ a, DecidablePred (Adj a)] (a : α) : Finset β :=
  univ.filter (fun b => Adj a b)

@[simp]
