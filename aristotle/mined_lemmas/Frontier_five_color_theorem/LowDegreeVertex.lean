import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

def LowDegreeVertex (s : Finset V) (G : SimpleGraph V) : Prop :=
  s.Nonempty → ∃ v ∈ s, (nbrs s G v).card ≤ 4 ∨
    ((nbrs s G v).card ≤ 5 ∧ ∃ u ∈ nbrs s G v, ∃ w ∈ nbrs s G v, u ≠ w ∧ ¬ G.Adj u w)

/-- The combinatorial hypothesis extracted from planarity: every graph reachable from `(s, G)`
by vertex deletions and contractions has a low degree vertex in the above sense.

Every planar graph satisfies this: planarity is preserved by vertex deletion and by edge
contraction, Euler's formula gives a vertex `v` of degree at most `5` in any planar graph, and
if `v` has degree exactly `5` then two of its neighbours must be non-adjacent, since otherwise
`K₆` (hence `K₅`) would be a subgraph. -/
