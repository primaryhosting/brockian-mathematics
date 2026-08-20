import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma succ_ne_pred (i : ZMod 17) : i + 1 ≠ i - 1 := by
  revert i; decide

