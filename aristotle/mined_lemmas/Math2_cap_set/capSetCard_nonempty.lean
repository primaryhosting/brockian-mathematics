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

lemma capSetCard_nonempty (n : ℕ) :
    {k | ∃ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = k}.Nonempty :=
  ⟨0, ∅, by simp, by simp⟩

/-- Every 3AP-free subset of `𝔽₃ⁿ` has at most `capSetCard n` elements. -/
