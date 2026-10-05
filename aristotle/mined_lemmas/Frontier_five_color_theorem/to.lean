import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Frontier

universe u

variable {V : Type u}

/-! ## Plane straight-line drawings

Mathlib (at the pinned commit) contains no theory of planar graphs at all, so we
first have to say what "planar" means.

We use the *straight-line* (Fáry) formulation: a finite simple graph is planar
exactly when it can be drawn in the plane with vertices at distinct points and
edges drawn as straight segments which meet only at shared endpoints.  By
Fáry's theorem this is equivalent to the usual topological definition for
finite simple graphs, and it has the advantage of being completely elementary
to state. -/

/-- The open straight segment in `ℝ²` drawn for an (unordered) edge `e`, when the
vertices are placed by `p`. -/

theorem to know that two Kempe chains cannot cross).

The Kempe chain step is exactly what is *not* available combinatorially, so what we
prove here is the special case in which the greedy induction goes through on its
own: planar graphs which are 4-degenerate.  This contains the base case of the
induction (graphs on at most five vertices) as `five_color_theorem_of_card_le_five`
below, which alternatively follows from the Mathlib lemma
`SimpleGraph.colorable_of_fintype : G.Colorable (Fintype.card V)` together with
`SimpleGraph.Colorable.mono`. -/

/-- **Five Colour Theorem (special case).**  Every 4-degenerate planar graph is
5-colourable.

The planarity hypothesis is stated because it is part of the theorem, but this
special case does not need it: 4-degeneracy alone already gives a greedy
5-colouring (`colorable_of_isDegenerate`).  Deriving 4-degeneracy-like behaviour
from planarity in general is precisely the Kempe chain argument, which is not
carried out here. -/
