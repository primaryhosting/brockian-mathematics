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

lemma ramR_4_4 : RamR G 4 4 18 := by
  have := ramR_step (G := G) (k := 3) (l := 3) (a := 9) (b := 9)
    (by norm_num) ramR_3_4 ramR_4_3
  simpa using this

/-- **Upper bound**: any graph on at least 18 vertices contains a monochromatic `K₄`. -/
