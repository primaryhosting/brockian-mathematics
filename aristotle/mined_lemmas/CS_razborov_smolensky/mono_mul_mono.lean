import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma mono_mul_mono (S T : Finset (Fin n)) :
    mono F S * mono F T = mono F (S ∪ T) := by
  classical
  funext x
  simp only [Pi.mul_apply, mono_apply, Finset.forall_mem_union]
  split_ifs <;> simp_all

