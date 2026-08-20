import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma Yprod_univ_apply (ζ : F) (x : Cube n) :
    Yprod F ζ (Finset.univ) x = ζ ^ ones x := by
  classical
  simp only [Yprod, Finset.prod_apply, yv_apply, ones]
  rw [Finset.prod_ite]
  simp

/-- Smolensky's dimension bound. -/
