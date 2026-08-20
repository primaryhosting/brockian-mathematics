import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma ee_mul_ee_neg (x : ZMod 17) : ee x * ee (-x) = 1 := by
  rw [← ee_add]; simp [ee_zero]

