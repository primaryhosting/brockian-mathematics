import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Yprod_mem_Deg (ζ : F) (S : Finset (Fin n)) : Yprod F ζ S ∈ Deg F n S.card :=
  prod_mem_Deg' _ _ (fun i _ => yv_mem_Deg ζ i)

