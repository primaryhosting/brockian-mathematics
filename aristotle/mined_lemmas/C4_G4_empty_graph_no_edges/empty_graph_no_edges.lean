import Mathlib
open Finset
namespace C4.G4

/-- The empty graph has no edges. -/

theorem empty_graph_no_edges {V : Type*} [Fintype V] [DecidableEq V] :
    (⊥ : SimpleGraph V).edgeFinset.card = 0 := by
  simp

/-- The edges of a graph and of its complement partition the edges of the complete
graph, so their numbers add up to `(card V).choose 2`. -/
