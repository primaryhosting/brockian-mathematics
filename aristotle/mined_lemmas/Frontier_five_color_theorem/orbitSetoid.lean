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

def orbitSetoid (f : Equiv.Perm α) : Setoid α where
  r a b := ∃ k : ℤ, (f ^ k) a = b
  iseqv :=
    { refl := fun a => ⟨0, by simp⟩
      symm := by
        rintro a b ⟨k, rfl⟩
        exact ⟨-k, by simp [← Equiv.Perm.mul_apply]⟩
      trans := by
        rintro a b c ⟨k, rfl⟩ ⟨l, rfl⟩
        exact ⟨l + k, by simp [zpow_add, Equiv.Perm.mul_apply]⟩ }

/-- The number of orbits of a permutation. -/
