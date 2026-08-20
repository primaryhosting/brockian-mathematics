import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem euler_char_tree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hc : G.Connected) (ha : G.IsAcyclic) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  SimpleGraph.IsTree.card_edgeFinset ⟨hc, ha⟩

/-- Placeholder statement as provided in the original file: it is literally `True`, so it carries
no topological content (in particular it is *not* the Jordan curve theorem). -/
