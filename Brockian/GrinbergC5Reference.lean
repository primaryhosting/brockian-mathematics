import Mathlib
import Brockian.AutomorphismFull

/-!
# Grinberg reference spine: the first `C₅` slice

This module records the first classical graph-theory slice extracted from Darij Grinberg,
*An introduction to graph theory*, arXiv:2308.04512v3 (June 7, 2025), CC0:

* Definition 2.6.3 and the discussion on pp. 29--30: the cycle graph `Cₙ`, its rotations,
  its reflections, and `Aut(Cₙ) = Dₙ` for `n > 2`;
* Theorem 4.5.10 on p. 121: entries of an adjacency-matrix power count walks.

The `Aut(C₅) ≃ D₅` result is already formalized in `Brockian.Automorphism.Full`, so it is
not duplicated here. The new content specializes Mathlib's general adjacency/walk theorem
to the repository's canonical `C₅`, derives the closed-walk trace identity, and checks the
length-two trace structurally from 2-regularity.

These are classical reference results, not Brockian novelty claims. The exact source and
classification map lives in
`provenance/reference-spines/grinberg-graph-theory-v3.yaml`.
-/

namespace Brockian.GrinbergC5Reference

open SimpleGraph
open Brockian.Automorphism

/-- Every vertex of the 5-cycle has degree two. This is the `n = 5` instance of
Mathlib's general degree theorem for cycle graphs. -/
theorem c5_degree_eq_two (v : Fin 5) : C5.degree v = 2 := by
  simpa [C5] using
    (SimpleGraph.cycleGraph_degree_three_le (n := 2) (v := v))

/-- The 5-cycle has five edges, obtained from 2-regularity and the handshaking lemma. -/
theorem c5_edge_count_eq_five : C5.edgeFinset.card = 5 := by
  have hdegrees : ∑ v : Fin 5, C5.degree v = 10 := by
    simp [c5_degree_eq_two]
  rw [C5.sum_degrees_eq_twice_card_edges] at hdegrees
  omega

/-- **Adjacency powers count walks on `C₅`.** The `(u,v)` entry of `A^n` is exactly
the number of length-`n` walks from `u` to `v`. This is Grinberg's Theorem 4.5.10,
specialized to the repository's canonical 5-cycle and natural-number adjacency matrix. -/
theorem c5_adjacency_power_counts_walks (n : ℕ) (u v : Fin 5) :
    (C5.adjMatrix ℕ ^ n) u v =
      Fintype.card {p : C5.Walk u v | p.length = n} :=
  C5.adjMatrix_pow_apply_eq_card_walk n u v

/-- Taking the trace of the adjacency-power identity counts all based closed walks of
length `n` on `C₅`. -/
theorem c5_adjacency_trace_counts_closed_walks (n : ℕ) :
    Matrix.trace (C5.adjMatrix ℕ ^ n) =
      ∑ v : Fin 5, Fintype.card {p : C5.Walk v v | p.length = n} := by
  simp only [Matrix.trace, Matrix.diag_apply, c5_adjacency_power_counts_walks]

/-- The length-two closed-walk count on `C₅` is ten: each of five base vertices has
two choices for the first step, and the second step must return. -/
theorem c5_adjacency_trace_sq_eq_ten :
    Matrix.trace (C5.adjMatrix ℕ ^ 2) = 10 := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two]
  simp_rw [SimpleGraph.adjMatrix_mul_self_apply_self]
  simp [c5_degree_eq_two]

/-- There are ten based closed walks of length two on `C₅`, in cardinality form. -/
theorem c5_closed_walks_length_two_eq_ten :
    (∑ v : Fin 5, Fintype.card {p : C5.Walk v v | p.length = 2}) = 10 := by
  rw [← c5_adjacency_trace_counts_closed_walks]
  exact c5_adjacency_trace_sq_eq_ten

end Brockian.GrinbergC5Reference
