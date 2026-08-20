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

@[simp] lemma symmPerm_apply (G : SimpleGraph V) (d : G.Dart) : symmPerm G d = d.symm := rfl

/-- A rotation system (combinatorial embedding) of a simple graph: a permutation of the darts
preserving the source vertex and acting transitively on the darts with a given source. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- The rotation permutation: the cyclic order of the darts around each vertex. -/
  rot : Equiv.Perm G.Dart
  /-- The rotation preserves the source vertex of a dart. -/
  rot_fst : ∀ d : G.Dart, (rot d).fst = d.fst
  /-- The rotation acts transitively on the set of darts with a given source vertex. -/
  rot_transitive : ∀ d d' : G.Dart, d.fst = d'.fst → ∃ k : ℤ, (rot ^ k) d = d'

namespace RotationSystem

variable {G : SimpleGraph V}

/-- The number of faces of a combinatorial embedding: the number of orbits of `rot ∘ symm`. -/
