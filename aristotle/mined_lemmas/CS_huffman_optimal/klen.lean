import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def klen (M : Multiset (β × ℕ)) : Multiset ℕ := M.map Prod.snd

