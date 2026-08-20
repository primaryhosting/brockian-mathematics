import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

noncomputable def orTarget {m : ℕ} (y : Fin m → Cube n → ZMod q) (x : Cube n) : ZMod q :=
  if ∀ i, y i x = 0 then 0 else 1

/-- Razborov's approximation of an `OR` gate by a low degree polynomial, for a given choice
of `l` subsets of the inputs. -/
