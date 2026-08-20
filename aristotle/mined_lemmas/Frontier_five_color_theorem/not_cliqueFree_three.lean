import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem not_cliqueFree_three (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ¬ G.CliqueFree 3 := by
  classical
  intro h
  refine h {a, b, c} ?_
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [G.symm hab, G.symm hbc, G.symm hca]
  · have h1 : a ≠ b := hab.ne
    have h2 : b ≠ c := hbc.ne
    have h3 : a ≠ c := (hca.ne).symm
    rw [Finset.card_insert_of_notMem (by simp_all), Finset.card_insert_of_notMem (by simp_all)]
    simp

omit [Fintype V] in
/-- In a triangle-free graph, no face of an embedding has exactly three sides. -/
