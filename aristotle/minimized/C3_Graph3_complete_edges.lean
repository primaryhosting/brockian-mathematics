import Mathlib
open Finset
namespace C3.Graph3

theorem complete_edges (n : ℕ) : (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
  simpa using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
