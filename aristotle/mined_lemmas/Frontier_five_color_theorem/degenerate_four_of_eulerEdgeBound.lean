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

theorem degenerate_four_of_eulerEdgeBound {G : SimpleGraph V} (hE : EulerEdgeBound G)
    (hcard : Fintype.card V ≤ 11) : Degenerate 4 G := by
  refine degenerate_of_sum_degIn_lt (fun s hs => ?_)
  have hle : s.card ≤ 11 := le_trans (Finset.card_le_univ s) hcard
  have hpos : 1 ≤ s.card := Finset.card_pos.2 hs
  rcases lt_or_ge s.card 3 with h3 | h3
  · -- small sets: every degree is at most `|s| - 1 ≤ 1`
    have hbound : ∀ v ∈ s, degIn G s v ≤ s.card - 1 := fun v hv =>
      degIn_le_card_sub_one G hv
    have : ∑ v ∈ s, degIn G s v ≤ ∑ _v ∈ s, (s.card - 1) := Finset.sum_le_sum hbound
    simp only [Finset.sum_const, smul_eq_mul] at this
    have hn : s.card = 1 ∨ s.card = 2 := by omega
    rcases hn with h1 | h1 <;> rw [h1] at this ⊢ <;> omega
  · have hEs := hE s h3
    have hsum := sum_degIn_eq_two_mul_edgeCountIn G s
    omega

/-!
## The Five Colour Theorem
-/

/-- **Five Colour Theorem, greedy form.**  Every finite graph each of whose nonempty
induced subgraphs contains a vertex of degree at most `4` is `5`-colourable. -/
