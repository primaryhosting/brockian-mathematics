import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma mem_Deg_of_le {f : Cube n → F} {D D' : ℕ} (hf : f ∈ Deg F n D) (h : D ≤ D') :
    f ∈ Deg F n D' := Deg_mono_le h hf

