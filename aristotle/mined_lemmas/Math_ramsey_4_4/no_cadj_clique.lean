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

theorem no_cadj_clique : ∀ a b c d : Fin 17,
    ¬ (cadj a b ∧ cadj a c ∧ cadj a d ∧ cadj b c ∧ cadj b d ∧ cadj c d) := by decide

/-- The Paley graph of order 17 has no `4`-clique. -/
