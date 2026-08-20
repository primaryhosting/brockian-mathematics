/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` lines to precede every command, including module
-- docstrings (`/-! ... -/`), so the header is repeated below as the module docstring.
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Math2

/-- The maximal size of a cap set in `𝔽₃ⁿ`, i.e. of a subset of `(Fin n → ZMod 3)` containing
no three-term arithmetic progression. -/

lemma capSetCard_bddAbove (n : ℕ) :
    BddAbove {k | ∃ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = k} :=
  ⟨3 ^ n, by
    rintro k ⟨A, -, rfl⟩
    simpa [card_space] using A.card_le_univ⟩

