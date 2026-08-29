import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def extBits (s : List Bool) (k : ℕ) : Finset (List Bool) :=
  (allBits k).image (fun t => s ++ t)

