import Mathlib
open Finset
namespace C2.Graph2

/-- The sum of the degrees of a finite simple graph is `2 * |E|`. -/

theorem sum_degrees_even {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (∑ v, G.degree v) := by
  rw [degree_sum_edges]
  exact even_two_mul _

/-- A finite tree on `n` vertices has `n - 1` edges. -/
