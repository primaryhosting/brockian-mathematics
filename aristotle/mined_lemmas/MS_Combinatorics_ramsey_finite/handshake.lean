import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

theorem handshake {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Even (∑ v, G.degree v) := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

