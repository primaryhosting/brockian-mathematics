import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem kraftL_cons (n : ℕ) (L : Multiset ℕ) :
    kraftL (n ::ₘ L) = (2:ℝ) ^ (-(n:ℤ)) + kraftL L := by
  simp [kraftL]

