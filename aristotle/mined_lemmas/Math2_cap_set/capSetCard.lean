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

noncomputable def capSetCard (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) ∧ #A = k}

