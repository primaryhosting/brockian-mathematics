import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem gcost_cons (C W : β → ℝ) (p : β × ℕ) (M : Multiset (β × ℕ)) :
    gcost C W (p ::ₘ M) = C p.1 + W p.1 * p.2 + gcost C W M := by simp [gcost]

