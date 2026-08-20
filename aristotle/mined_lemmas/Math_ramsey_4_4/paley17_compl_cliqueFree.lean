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

theorem paley17_compl_cliqueFree : ∀ t : Finset (Fin 17), ¬ paley17ᶜ.IsNClique 4 t := by
  intro t ht
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩ := exists_adj_of_isNClique_four ht
  have key : ∀ i j : Fin 17, paley17ᶜ.Adj i j → cadj i j = true := by
    intro i j h
    rw [SimpleGraph.compl_adj] at h
    simp only [cadj, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
    exact ⟨h.1, by simpa [paley17] using h.2⟩
  exact no_cadj_clique a b c d
    ⟨key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4, key _ _ h5, key _ _ h6⟩

end Math

import Mathlib
import RequestProject.RamseyUpper
import RequestProject.RamseyLower

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# The Ramsey number `R(4,4) = 18`
-/

namespace Math

/-- `IsRamsey k l N` says that every graph on `N` vertices contains either a clique of
size `k` or an independent set of size `l`. -/
