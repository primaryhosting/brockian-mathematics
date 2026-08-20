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

noncomputable def numOrbits (f : Equiv.Perm α) : ℕ := Nat.card (Quotient (orbitSetoid f))

/-- If no nontrivial power `f ^ i`, `0 < i < n`, fixes any point -- i.e. every orbit of `f` has at
least `n` elements -- then `f` has at most `#α / n` orbits. -/
