import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def allBits : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (allBits n).image (fun l => false :: l) ∪ (allBits n).image (fun l => true :: l)

