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

lemma comap_compl (f : V ↪ W) (G : SimpleGraph W) :
    (SimpleGraph.comap f G)ᶜ = SimpleGraph.comap f Gᶜ := by
  ext x y
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, ne_eq, f.apply_eq_iff_eq]

