import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Deg_eq_span_monoFinset (D : ℕ) :
    Deg F n D = Submodule.span F (monoFinset F n D : Set (Cube n → F)) := by
  rw [coe_monoFinset]; rfl

