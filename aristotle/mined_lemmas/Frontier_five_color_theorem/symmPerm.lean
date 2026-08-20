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

def symmPerm (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm SimpleGraph.Dart.symm SimpleGraph.Dart.symm_symm

