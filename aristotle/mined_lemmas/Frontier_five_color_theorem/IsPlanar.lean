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

def IsPlanar [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ R : RotationSystem G,
    2 * (Nat.card G.ConnectedComponent : ℤ) ≤ (Fintype.card V : ℤ) - (Nat.card G.edgeSet : ℤ)
      + (R.faceCount : ℤ) + (isolatedCount G : ℤ)

section

variable [Fintype V] {G : SimpleGraph V}

/-- If every vertex has at least two neighbours, the rotation has no fixed dart. -/
