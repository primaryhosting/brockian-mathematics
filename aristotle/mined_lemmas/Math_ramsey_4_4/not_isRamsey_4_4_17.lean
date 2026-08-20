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

theorem not_isRamsey_4_4_17 : ¬ IsRamsey 4 4 17 := by
  intro h
  rcases h paley17 with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact paley17_cliqueFree s hs
  · exact paley17_compl_cliqueFree s hs

/-- **The Ramsey number `R(4,4)` equals `18`.** -/
