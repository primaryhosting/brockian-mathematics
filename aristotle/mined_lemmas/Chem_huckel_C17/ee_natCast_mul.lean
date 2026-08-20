import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma ee_natCast_mul (n : ℕ) (x : ZMod 17) : ee ((n : ZMod 17) * x) = (ee x) ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih =>
      have h : ((n + 1 : ℕ) : ZMod 17) * x = (n : ZMod 17) * x + x := by push_cast; ring
      rw [h, ee_add, ih, pow_succ]

