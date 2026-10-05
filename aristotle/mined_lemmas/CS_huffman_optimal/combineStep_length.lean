import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem combineStep_length (w : α → ℝ) (ts : List (HTree α)) (h : 2 ≤ ts.length) :
    (combineStep w ts).length + 1 = ts.length := by
  obtain ⟨t1, t2, rest, heq, _, _, _, hlen⟩ := combineStep_spec w ts h
  rw [heq]
  simpa using hlen

/-- Huffman's algorithm: iterate `combineStep` until a single tree remains. -/
