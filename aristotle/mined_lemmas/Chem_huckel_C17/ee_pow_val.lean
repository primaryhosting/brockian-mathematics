import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma ee_pow_val (k m : ZMod 17) : ee (k * m) = (ee m) ^ k.val := by
  have h : ((k.val : ℕ) : ZMod 17) = k := by simp
  calc ee (k * m) = ee (((k.val : ℕ) : ZMod 17) * m) := by rw [h]
    _ = (ee m) ^ k.val := ee_natCast_mul _ _

