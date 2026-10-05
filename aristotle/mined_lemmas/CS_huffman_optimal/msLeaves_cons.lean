import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem msLeaves_cons (t : HTree α) (M : Multiset (HTree α)) :
    msLeaves (t ::ₘ M) = t.leaves + msLeaves M := by simp [msLeaves]

