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

lemma capSetCard_le {n B : ℕ}
    (h : ∀ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) → #A ≤ B) :
    capSetCard n ≤ B :=
  csSup_le (capSetCard_nonempty n) (by rintro k ⟨A, hA, rfl⟩; exact h A hA)

/-- Quantitative form of the cap set bound: for every `ε > 0`, all sufficiently large `n` are such
that every 3AP-free subset of `𝔽₃ⁿ` has size at most `ε * 3 ^ n`.

This is deduced from Roth's theorem for finite abelian groups (`roth_3ap_theorem` in Mathlib),
applied to the group `𝔽₃ⁿ = (Fin n → ZMod 3)`. -/
