import Mathlib
open Finset
namespace Frontier.CombinatoricsGraph

theorem handshake {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (∑ v, G.degree v) := by
  rw [G.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _
