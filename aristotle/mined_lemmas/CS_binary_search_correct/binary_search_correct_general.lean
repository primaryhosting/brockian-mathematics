import Mathlib

/-!
# Binary search over an arbitrary linear order (Mathlib version)

This is the same development as in `RequestProject/Main.lean`, but for arrays over an
arbitrary `LinearOrder`.  The main result is `CS.binary_search_correct_general`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Binary search for `key` in the index range `[lo, hi)` of the "array" `f`. -/

theorem binary_search_correct_general [Inhabited α] (a : Array α) (key : α)
    (hsorted : ∀ i j, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    ((∃ i, arrayBSearchGen a key = some i) ↔ ∃ i, i < a.size ∧ a[i]! = key) ∧
      ∀ i, arrayBSearchGen a key = some i → i < a.size ∧ a[i]! = key := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨-, h2, h3⟩ := bsearchRangeGen_eq_some hi
    exact ⟨i, h2, h3⟩
  · rintro ⟨i, hi1, hi2⟩
    rcases hnone : arrayBSearchGen a key with _ | j
    · exact absurd hi2 (bsearchRangeGen_eq_none hsorted hnone i (Nat.zero_le _) hi1)
    · exact ⟨j, rfl⟩
  · intro i hi
    obtain ⟨-, h2, h3⟩ := bsearchRangeGen_eq_some hi
    exact ⟨h2, h3⟩

end CS

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: a Lean 4 module docstring (`/-! ... -/`) must be the first *command* in a
file, and `import` commands must precede every other command.  Since the required header above
is a module docstring, this file cannot contain any `import` line, so the development below is
carried out over `Int` using only the Lean 4 core library.  A fully general Mathlib version, for
an arbitrary `LinearOrder`, is proved in `RequestProject/BinarySearchGeneral.lean` as
`CS.binary_search_correct_general`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- Binary search for `key` in the index range `[lo, hi)` of the "array" `f`.
Returns `some i` (with `f i = key`) if the key is found there, and `none` otherwise. -/
