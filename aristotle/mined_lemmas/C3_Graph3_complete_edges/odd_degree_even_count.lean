import Mathlib
open Finset
namespace C3.Graph3

theorem odd_degree_even_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (univ.filter (fun v => Odd (G.degree v))).card := by
  simpa [Set.toFinset_setOf] using G.even_card_odd_degree_vertices
end C3.Graph3

