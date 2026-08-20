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

noncomputable def faceCount (R : RotationSystem G) : ℕ := numOrbits (R.rot * symmPerm G)

end RotationSystem

/-- The number of isolated vertices of `G`. An isolated vertex carries no dart, hence lies on no
face in the sense of `faceCount`, although in a drawing it does lie inside a face; the Euler
characteristic below is corrected accordingly. -/
