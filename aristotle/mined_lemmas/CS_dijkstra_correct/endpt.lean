import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/

def endpt : V → List V → V
  | u, [] => u
  | _, v :: l => endpt v l

/-- The shortest-path distance from `s` to `t`: the infimum of the weights of all walks
from `s` to `t` (`⊤` if `t` is unreachable). -/
