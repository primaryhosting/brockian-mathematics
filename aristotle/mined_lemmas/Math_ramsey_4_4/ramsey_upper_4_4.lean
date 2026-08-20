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

theorem ramsey_upper_4_4 {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (hW : 18 ≤ Fintype.card W) :
    (∃ t : Finset W, G.IsNClique 4 t) ∨ (∃ t : Finset W, Gᶜ.IsNClique 4 t) := by
  have := ramR_4_4 (G := G) Finset.univ (by simpa using hW)
  rcases this with ⟨t, _, ht⟩ | ⟨t, _, ht⟩
  · exact Or.inl ⟨t, ht⟩
  · exact Or.inr ⟨t, ht⟩

end Math

import Mathlib

/-!
# Lower bound for the Ramsey number R(4,4)

The Paley graph on 17 vertices (`Math.paley17`) has no clique of size 4 and no
independent set of size 4, which shows `R(4,4) > 17`.
-/

namespace Math

/-- The nonzero quadratic residues modulo 17. -/
