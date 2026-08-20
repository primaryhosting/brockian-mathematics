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

lemma ramR_two_right (k : ℕ) : RamR G k 2 k :=
  RamR.compl (ramR_two_left k)

/-- The basic inductive step `R(k+1, l+1) ≤ R(k, l+1) + R(k+1, l)`. -/
