import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem pythagorean {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V)
    (h : inner ℝ x y = (0 : ℝ)) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]; ring

/-- A finite connected acyclic graph (a tree) has one fewer edge than it has vertices. -/
