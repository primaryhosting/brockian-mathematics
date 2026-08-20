import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## Overview

The Four Colour Theorem (Appel–Haken) states that every planar graph can be properly
coloured with four colours.  Its only known proofs rely on a massive computer-assisted
case analysis, so the theorem itself is not proved here.  What this file contains is:

* a formalisation of the notion of a *planar graph*, via crossing-free drawings in the
  plane (`Frontier.PlanarEmbedding`, `Frontier.IsPlanar`);
* the formal statement of the Four Colour Theorem (`Frontier.FourColorConjecture`);
* structural facts about planarity: it is inherited by subgraphs
  (`Frontier.IsPlanar.mono`, `Frontier.IsPlanar.comap`, `Frontier.IsPlanar.induce`);
* examples showing the notion is not vacuous (`Frontier.isPlanar_bot_fin`,
  `Frontier.isPlanar_top_fin_two`);
* base cases which are unconditionally proved
  (`Frontier.colorable_four_of_card_le`, `Frontier.colorable_four_of_bot`);
* and, as the main target, a **Lean-checked reduction**
  (`Frontier.four_color_statement`): the Four Colour Theorem for arbitrary planar graphs
  follows from — and is therefore equivalent to — the Four Colour Theorem for *finite,
  connected* planar graphs *of minimum degree at least four*.  The reduction to the
  finite case is a de Bruijn–Erdős style compactness argument; the reduction to the
  connected case is the decomposition of a graph into its connected components; and the
  reduction to minimum degree four is the classical minimal-counterexample argument
  which deletes a vertex with at most three neighbours.  Weaker intermediate forms are
  also recorded (`Frontier.four_color_statement_finite`,
  `Frontier.four_color_statement_finite_connected`).
-/

namespace Frontier

/-! ## Planar graphs -/

/-- A *plane drawing* (planar embedding) of a simple graph `G`:

* every vertex `v` is sent to a point `pt v` of the plane, injectively;
* every edge `uv` is drawn as an arc `arc u v`, i.e. the image of a continuous injective
  map defined on `[0,1]`, whose endpoints are `pt u` and `pt v`;
* two distinct edges meet only in the images of their common endpoints;
* no arc passes through the point of a vertex which is not one of its endpoints.

This is the standard notion of a drawing of a graph in the plane without crossings. -/
structure PlanarEmbedding {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pt : V → ℝ × ℝ
  /-- Distinct vertices get distinct points. -/
  pt_inj : Function.Injective pt
  /-- The set of points of the plane covered by the arc drawing the edge `uv`. -/
  arc : V → V → Set (ℝ × ℝ)
  /-- The arc drawing `uv` is the arc drawing `vu`. -/
  arc_symm : ∀ u v, arc u v = arc v u
  /-- The arc drawing an edge really is an arc from one endpoint to the other. -/
  arc_isArc : ∀ {u v : V}, G.Adj u v → ∃ g : ℝ → ℝ × ℝ,
    ContinuousOn g (Set.Icc 0 1) ∧ Set.InjOn g (Set.Icc 0 1) ∧
      g 0 = pt u ∧ g 1 = pt v ∧ arc u v = g '' Set.Icc 0 1
  /-- Two distinct edges meet only at points coming from common endpoints. -/
  arc_inter : ∀ {u v x y : V}, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    arc u v ∩ arc x y ⊆ pt '' ({u, v} ∩ {x, y})
  /-- An arc avoids the points of all vertices other than its endpoints. -/
  pt_notMem : ∀ {u v w : V}, G.Adj u v → w ≠ u → w ≠ v → pt w ∉ arc u v

/-- A graph is *planar* when it admits a drawing in the plane without crossings. -/

theorem colorable_four_of_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 4) : G.Colorable 4 :=
  (SimpleGraph.colorable_of_fintype G).mono h

/-- Base case: the edgeless graph is four-colourable. -/
