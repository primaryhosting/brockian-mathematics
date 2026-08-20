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

theorem isRamsey_4_4_18 : IsRamsey 4 4 18 := by
  intro G
  classical
  exact ramsey_upper_4_4 G (by simp)

/-- The Paley graph on 17 vertices witnesses that `K₁₇` admits a two-colouring with no
monochromatic `K₄`. -/
