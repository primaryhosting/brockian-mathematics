import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

noncomputable def isolatedCount (G : SimpleGraph V) : ℕ := Nat.card {v : V // ∀ w, ¬ G.Adj v w}

/-- A finite simple graph is *planar* if it admits a combinatorial embedding (rotation system)
whose corrected Euler characteristic `#V - #E + #F + #(isolated vertices)` is at least twice the
number of connected components of `G`.

Justification of the definition. The orbits of `rot ∘ symm` are the faces of the embeddings of
the individual connected components of `G` (isolated vertices contribute no orbit, whence the
correction term). A connected graph with at least one edge embedded in a closed orientable
surface of genus `g` satisfies `#V - #E + #F = 2 - 2g ≤ 2`, with equality exactly when `g = 0`,
i.e. when the component is drawn in the sphere -- equivalently, in the plane. Summing over the
`c` components, `#V - #E + #F + #(isolated vertices) = 2c - 2 ∑ gᵢ`, which is `≥ 2c` if and only
if every component has genus `0`, i.e. if and only if `G` is planar. -/
