import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A convex polyhedron (for instance a fullerene cage such as C₆₀) gives rise to a *plane map*:

* a graph `G` on the set `Vt` of vertices;
* the dual graph `D` on the set `Ft` of faces;
* a bijection `dual` between the edges of `G` and the edges of `D` — each edge of the
  polyhedron is shared by exactly two faces, and dually.

Planarity (i.e. the fact that the map lives on a sphere) is encoded by the classical
*interdigitating spanning trees* property: there is a spanning tree `T` of the graph such
that the duals of the remaining edges form a spanning tree of the dual graph.  This is the
combinatorial content of planarity used in the standard proof of Euler's formula, and it is
the hypothesis of `Chem.euler_polyhedron` below, whose conclusion is `V - E + F = 2`.

The hypotheses are not vacuous: `Chem.tetrahedron_euler` verifies them for the tetrahedron
(whose graph and dual graph are both `K₄`), and `Chem.fullerene_twelve_pentagons` derives
from Euler's formula the chemical fact that a trivalent cage whose faces are pentagons and
hexagons has exactly twelve pentagons.
-/

namespace Chem

open SimpleGraph

/-- For a set `S` of edges of a graph `H` spanning a tree, `#S + 1 = #vertices`. -/

def star4 : Set (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3)}

/-- Duality on the edges of the tetrahedron: an edge is sent to the complementary pair of
vertices, i.e. to the pair of faces containing it. -/
