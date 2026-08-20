import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Deg_mono_le {D D' : ℕ} (h : D ≤ D') : Deg F n D ≤ Deg F n D' := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨S, hS, rfl⟩
  exact mono_mem_Deg (hS.trans h)

