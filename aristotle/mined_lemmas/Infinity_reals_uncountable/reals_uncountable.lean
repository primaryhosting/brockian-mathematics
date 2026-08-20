/-
# Reals Uncountable
Category: Frontier — Set Theory
Target: Infinity.reals_uncountable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Reals Uncountable
Category: Frontier — Set Theory
Target: Infinity.reals_uncountable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Infinity

/-- The real numbers are uncountable: there is no surjection from `ℕ` onto `ℝ`.

The key input is Mathlib's `Cardinal.not_countable_real` (from
`Mathlib/Analysis/Real/Cardinality.lean`), which states that `(Set.univ : Set ℝ)`
is not countable; it in turn follows from `Cardinal.mk_real : #ℝ = 𝔠`. -/

theorem reals_uncountable : ¬ ∃ f : ℕ → ℝ, Function.Surjective f := by
  rintro ⟨f, hf⟩
  refine Cardinal.not_countable_real ?_
  rw [← Set.range_eq_univ.mpr hf]
  exact Set.countable_range f

/-- Equivalently, `ℝ` is not a countable type. -/
