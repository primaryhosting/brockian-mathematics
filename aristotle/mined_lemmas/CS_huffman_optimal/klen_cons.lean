import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem klen_cons (p : β × ℕ) (M : Multiset (β × ℕ)) :
    klen (p ::ₘ M) = p.2 ::ₘ klen M := by simp [klen]

