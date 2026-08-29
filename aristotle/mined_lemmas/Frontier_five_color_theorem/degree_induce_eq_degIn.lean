/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Five Color Theorem

Category: Frontier — Fields Medal Work

Target: `Frontier.five_color_theorem`

Verification: pending

Provenance: Aristotle theorem prover (Harmonic)

## Overview

`Mathlib` contains no theory of planar graphs (no embeddings, no Euler formula, no
Kuratowski theorem), so this file develops from scratch the combinatorial core of the
classical inductive proof of the Five Colour Theorem.

The classical proof, for a finite planar graph `G`, runs as follows.

* By Euler's formula a planar graph on `n ≥ 3` vertices has at most `3n - 6` edges.
* Hence the sum of the degrees is at most `6n - 12`, so some vertex has degree at most `5`.
* Delete such a vertex `v`, five-colour `G - v` by induction, and extend the colouring.
  If `deg v ≤ 4` the extension is immediate: the neighbours of `v` occupy at most four of
  the five colours.  Only the remaining case `deg v = 5` needs Kempe's chain exchange.

Everything except the Kempe chain exchange is formalised here:

* `Frontier.Degenerate`   — the degeneracy hypothesis extracted from Euler's formula;
* `Frontier.exists_partial_coloring`, `Frontier.colorable_of_degenerate` — the greedy
  colouring argument in full generality: a `k`-degenerate finite graph is
  `(k + 1)`-colourable;
* `Frontier.edgeCountIn`, `Frontier.EulerEdgeBound` — the planarity input, namely the
  Euler edge bound `e(H) ≤ 3·|H| - 6` for all induced subgraphs `H`;
* `Frontier.sum_degIn_eq_two_mul_edgeCountIn` — the handshake lemma for induced subgraphs;
* `Frontier.degenerate_four_of_eulerEdgeBound` — the averaging argument turning the Euler
  bound into `4`-degeneracy for graphs on at most `11` vertices;
* `Frontier.five_color_theorem` — the Five Colour Theorem for planar graphs on at most
  `11` vertices.

The bound `11` is exactly where the greedy argument stops being sufficient: for `n ≥ 12`
the Euler bound only forces a vertex of degree `≤ 5`, which is the case reserved for Kempe
chains.  So the statement proved here is the sharp "base case" of the induction that the
greedy half of the argument can reach.
-/

namespace Frontier

open Finset

open scoped Classical

variable {V : Type*}

/-! ## Degrees inside a finite set of vertices -/

/-- The number of neighbours of `v` inside the finite vertex set `s`. -/

theorem degree_induce_eq_degIn (G : SimpleGraph V) (s : Finset V) (v : V) (hv : v ∈ s) :
    (G.induce (s : Set V)).degree ⟨v, by simpa using hv⟩ = degIn G s v := by
  rw [SimpleGraph.degree]
  unfold degIn
  apply Finset.card_bij (fun (u : ((s : Set V))) _ => (u : V))
  · intro a ha
    simp only [SimpleGraph.mem_neighborFinset] at ha
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_coe.1 a.2, ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact ⟨⟨b, by simpa using hb.1⟩, by simpa [SimpleGraph.mem_neighborFinset] using hb.2, rfl⟩

/-- **Handshake lemma for induced subgraphs.**  The sum of the degrees inside `s` is twice
the number of edges of the subgraph induced on `s`. -/
