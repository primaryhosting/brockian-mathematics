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

lemma ramR_3_4 : RamR G 3 4 9 := by
  have := ramR_step_parity (G := G) (k := 2) (l := 3) (a := 4) (b := 6)
    (by norm_num) (by norm_num) (by decide) (by decide) ramR_2_4 ramR_3_3
  simpa using this

