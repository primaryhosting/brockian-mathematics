import Mathlib
open Finset
namespace C2.Graph2

/-- The sum of the degrees of a finite simple graph is `2 * |E|`. -/

theorem tree_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.IsTree) : G.edgeFinset.card + 1 = Fintype.card V :=
  ht.card_edgeFinset

end C2.Graph2

