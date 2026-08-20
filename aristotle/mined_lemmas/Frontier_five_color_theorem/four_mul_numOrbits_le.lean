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

theorem four_mul_numOrbits_le [Finite α] (f : Equiv.Perm α)
    (h1 : ∀ a : α, f a ≠ a) (h2 : ∀ a : α, f (f a) ≠ a) (h3 : ∀ a : α, f (f (f a)) ≠ a) :
    4 * numOrbits f ≤ Nat.card α := by
  refine numOrbits_mul_le f 4 ?_
  intro a i hi hi4
  interval_cases i
  · simpa using h1 a
  · simpa [pow_two, Equiv.Perm.mul_apply] using h2 a
  · simpa [pow_succ, Equiv.Perm.mul_apply] using h3 a

/-- A permutation acting transitively on a nonempty type has exactly one orbit. -/
