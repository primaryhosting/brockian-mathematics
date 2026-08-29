import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem gcost_mono_length (C W : β → ℝ) (b : β) {x y : ℕ} (hW : 0 ≤ W b) (hxy : x ≤ y)
    (M : Multiset (β × ℕ)) :
    gcost C W ((b, x) ::ₘ M) ≤ gcost C W ((b, y) ::ₘ M) := by
  have : (x:ℝ) ≤ (y:ℝ) := by exact_mod_cast hxy
  simp only [gcost_cons]
  nlinarith

/-- **Normalisation.** If `b1, b2` are of minimal weight, any Kraft-admissible length
assignment can be replaced by one of no larger cost in which `b1` and `b2` receive the same
positive length. -/
