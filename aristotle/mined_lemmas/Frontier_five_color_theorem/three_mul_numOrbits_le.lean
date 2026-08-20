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

theorem three_mul_numOrbits_le [Finite α] (f : Equiv.Perm α)
    (h1 : ∀ a : α, f a ≠ a) (h2 : ∀ a : α, f (f a) ≠ a) :
    3 * numOrbits f ≤ Nat.card α := by
  refine numOrbits_mul_le f 3 ?_
  intro a i hi hi3
  interval_cases i
  · simpa using h1 a
  · simpa [pow_two, Equiv.Perm.mul_apply] using h2 a

/-- If every orbit of `f` has at least four elements then `f` has at most `#α / 4` orbits. -/
