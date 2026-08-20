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

theorem four_color_theorem_of_trianglefree (h : IsHereditarilyPlanar G) (htf : G.CliqueFree 3) :
    G.Colorable 4 :=
  colorable_of_isDegenerate 3 (isDegenerate_of_trianglefree h htf)

end Frontier

import Mathlib
import RequestProject.Orbits
import RequestProject.Planar
import RequestProject.Coloring

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The five colour theorem

The five colour theorem states that every planar graph can be properly coloured with five
colours. Its classical proof runs by induction on the number of vertices: a planar graph always
has a vertex `v` of degree at most `5` (a consequence of Euler's formula), one colours `G - v`
inductively, and if all five colours occur among the neighbours of `v` one recolours using a
*Kempe chain* argument, which relies on the planarity of the embedding (a combinatorial form of
the Jordan curve theorem).

This file develops the following, all of it proved from scratch on top of a combinatorial
(rotation-system) notion of planarity introduced in `RequestProject.Planar`:

* Euler's edge bound `#E ≤ 3 #V - 6` for planar graphs (`Frontier.planar_edge_bound`) and the
  refinement `#E ≤ 2 #V - 4` for triangle-free planar graphs
  (`Frontier.planar_trianglefree_edge_bound`);
* every nonempty planar graph has a vertex of degree at most `5`
  (`Frontier.exists_degree_le_five`); a triangle-free one has a vertex of degree at most `3`
  (`Frontier.exists_degree_le_three`), and one with at most eleven vertices has a vertex of
  degree at most `4` (`Frontier.exists_degree_le_four_of_card_le_eleven`);
* greedy colouring of degenerate graphs (`Frontier.colorable_of_isDegenerate`);
* consequently the **six colour theorem** (`Frontier.six_color_theorem`) and the
  **four colour theorem for triangle-free planar graphs**
  (`Frontier.four_color_theorem_of_trianglefree`);
* the special cases of the five colour theorem collected in `Frontier.five_color_theorem`
  below: planar graphs that are `4`-degenerate, planar graphs on at most eleven vertices
  (`Frontier.five_color_theorem_of_card_le_eleven`), and triangle-free planar graphs.

The general five colour theorem (which needs the Kempe chain argument, hence a combinatorial
Jordan curve theorem for rotation systems) is **not** proved here.
-/

namespace Frontier

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A graph with at most five vertices is `4`-degenerate. -/
