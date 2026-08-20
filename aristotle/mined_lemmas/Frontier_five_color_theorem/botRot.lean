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

def botRot {α : Type*} : RotationSystem (⊥ : SimpleGraph α) where
  rot := 1
  rot_fst := fun _ => rfl
  rot_transitive := fun d _ _ => (d.adj).elim

/-- Non-vacuity check: an edgeless graph is planar (with equality in Euler's formula: each of its
`n` vertices is a component, contributing one vertex and one face). -/
