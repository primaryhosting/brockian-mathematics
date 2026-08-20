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

theorem isHereditarilyPlanar_bot : IsHereditarilyPlanar (⊥ : SimpleGraph V) := by
  intro s
  have h : (⊥ : SimpleGraph V).induce (↑s : Set V) = (⊥ : SimpleGraph (↑s : Set V)) := by
    ext a b
    simp
  rw [h]
  exact isPlanar_bot

/-- A hereditarily planar graph on at most eleven vertices is `4`-degenerate. -/
