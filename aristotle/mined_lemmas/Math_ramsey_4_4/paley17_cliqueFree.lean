import Mathlib

/-!
# Upper bound for the Ramsey number R(4,4)

This file develops, from scratch, the classical inductive bounds on two-colour Ramsey
numbers, culminating in `Math.ramsey_upper_4_4`: every graph on a vertex set of size at
least `18` contains a `4`-clique or an independent set of size `4`.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- The neighbours of `v` inside `s` (excluding `v` itself). -/

theorem paley17_cliqueFree : ∀ t : Finset (Fin 17), ¬ paley17.IsNClique 4 t := by
  intro t ht
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩ := exists_adj_of_isNClique_four ht
  exact no_padj_clique a b c d ⟨h1, h2, h3, h4, h5, h6⟩

/-- The complement of the Paley graph of order 17 has no `4`-clique. -/
