import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem card_extBits (s : List Bool) (k : ℕ) : (extBits s k).card = 2 ^ k := by
  rw [extBits, Finset.card_image_of_injective _ (fun x y h => by simpa using h), card_allBits]

