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

theorem dual4_image_compl : dual4 '' ((⊤ : SimpleGraph (Fin 4)).edgeSet \ star4) = star4 := by
  have hd : (⊤ : SimpleGraph (Fin 4)).edgeSet \ star4 = {s(1, 2), s(1, 3), s(2, 3)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b => fin_cases a <;> fin_cases b <;> simp [star4]
  have e1 : dual4 s(1, 2) = s(0, 3) := by decide
  have e2 : dual4 s(1, 3) = s(0, 2) := by decide
  have e3 : dual4 s(2, 3) = s(0, 1) := by decide
  rw [hd]
  simp only [Set.image_insert_eq, Set.image_singleton, e1, e2, e3]
  ext e
  simp only [star4, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The hypotheses of `Chem.euler_polyhedron` are satisfiable: the tetrahedron is a plane
map with interdigitating spanning trees, and indeed `4 - 6 + 4 = 2`. -/
