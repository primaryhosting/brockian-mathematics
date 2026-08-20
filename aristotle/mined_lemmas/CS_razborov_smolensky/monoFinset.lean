import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

noncomputable def monoFinset (F : Type*) [Field F] (n D : ℕ) : Finset (Cube n → F) := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ D)).image (mono F)

