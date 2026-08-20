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

def paley17 : SimpleGraph (Fin 17) where
  Adj i j := padj i j = true
  symm := by
    intro i j h
    rw [padj_symm]
    exact h
  loopless := ⟨by
    intro i h
    rw [padj_irrefl i] at h
    exact Bool.noConfusion h⟩

instance : DecidableRel paley17.Adj := fun i j =>
  inferInstanceAs (Decidable (padj i j = true))

/-- Adjacency in the complement of the Paley graph, as a boolean function. -/
